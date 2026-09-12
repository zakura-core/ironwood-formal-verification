import Zcash.Snark.ZeroKnowledge.StoredActionInitialCost
import Zcash.Snark.ZeroKnowledge.StoredActionOracleViewCost
import Zcash.Snark.ZeroKnowledge.ActionCacheCost
import Zcash.Snark.ZeroKnowledge.ActionOracleBits

/-!
# The complete original Action oracle simulator with execution costs

Public initialization, the full bit-driven proof and oracle view, and
conflict-checked cache programming are composed here. The returned counter
retains all work on every failure branch. Setup and key are supplied as stored
inputs; their representation theorem uses the original Action compiler data.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

-- Compose established program identities without expanding the prover or compiler.
attribute [local irreducible] storedActionOracleViewCosted programOracleView plonkRawOracleView
  plonkVerifierSimulatorFromTape plonkPublicPolynomialsFromRows actionReferenceKey

/-- Run the complete stored-input simulator and retain initialization, view, and cache costs. -/
def storedActionOracleSimulatorCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) (bits : List Bool) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) × ℕ :=
  let initial := storedActionInitialCosted fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
    inputs setup (vkTranscriptRepr, read + 1)
  let view := storedActionOracleViewCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits initial.1
  let programmed := programOracleViewCosted cache view.1
  (programmed.1, initial.2 + view.2 + programmed.2 + 4)

set_option maxRecDepth 10000 in
/-- Erasing costs gives exactly `actionOracleSimulatorFromBits` with the actual Action compiler and codecs. -/
theorem storedActionOracleSimulatorCosted_result
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (bits : Fin (actionOracleSimulatorBitCount inputs.length 11) → Bool) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG :=
      actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (storedActionOracleSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup
      (StoredPlonkKey.encode (actions := inputs.length) (k := 11) vk) vkTranscriptRepr cache (List.ofFn bits)).1 =
      actionOracleSimulatorFromBits urs rfl (fun index : Fin inputs.length => inputs[index.val])
        vkTranscriptRepr cache bits := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG :=
    actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
  let initial := storedActionInitialCosted fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
    inputs setup (vkTranscriptRepr, read + 1)
  have hi : initial.1 = actionOracleInitial urs vkTranscriptRepr
      (fun index : Fin inputs.length => inputs[index.val]) :=
    storedActionInitialCosted_result fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
      inputs generators W U (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
      (vkTranscriptRepr, read + 1)
  have hv := storedActionOracleViewCosted_result fieldCosts ipaCosts node equal read omegaAccess inputs
    generators W U (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit) vk bits initial.1
  dsimp only at hv
  conv at hv =>
    rhs
    rw [hi]
  change (programOracleViewCosted cache
    (storedActionOracleViewCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup
      (StoredPlonkKey.encode (actions := inputs.length) (k := 11) vk) (List.ofFn bits) initial.1).1).1 = _
  rw [programOracleViewCosted_result]
  exact congrArg (programOracleView cache) hv

end Zcash.Snark.ZeroKnowledge
