import Zcash.Snark.ZeroKnowledge.StoredActionOracleSimulatorBound

/-!
# Statistical simulation by the complete counted implementation

The same uniform bit law drives the stored-input implementation whose complete
execution cost is bounded. Only its original attempt/cache output is observed;
the auxiliary cost counter is discarded. Exact program equality transfers the
existing statistical random-oracle theorem to this implementation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common

attribute [local irreducible] storedActionOracleSimulatorCosted actionOracleSimulatorFromBits actionReferenceKey

/-- The complete counted simulator driven by its original uniform Boolean input tape. -/
noncomputable def storedActionOracleBitSimulator
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG :=
    actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
  (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount inputs.length 11) → Bool)).map fun bits =>
    (storedActionOracleSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup
      (StoredPlonkKey.encode (actions := inputs.length) (k := 11) vk) vkTranscriptRepr cache (List.ofFn bits)).1

set_option maxRecDepth 10000 in
/-- The implementation with a proved runtime bound has exactly the existing fixed-bit simulator law. -/
theorem storedActionOracleBitSimulator_law
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    storedActionOracleBitSimulator fieldCosts ipaCosts node equal read omegaAccess inputs generators W U
      vkTranscriptRepr cache =
      actionOracleBitSimulator ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
        (fun index : Fin inputs.length => inputs[index.val]) vkTranscriptRepr cache := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG :=
    actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
  have hr : (fun bits : Fin (actionOracleSimulatorBitCount inputs.length 11) → Bool =>
      (storedActionOracleSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup
        (StoredPlonkKey.encode (actions := inputs.length) (k := 11) vk) vkTranscriptRepr cache (List.ofFn bits)).1) =
      actionOracleSimulatorFromBits urs rfl (fun index : Fin inputs.length => inputs[index.val]) vkTranscriptRepr cache := by
    funext bits
    exact storedActionOracleSimulatorCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U vkTranscriptRepr cache bits
  exact congrArg (fun run =>
    (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount inputs.length 11) → Bool)).map run) hr

/-- The complete counted implementation satisfies the existing two-sided statistical oracle bound. -/
theorem storedActionOracleBit_simulation_error_bound [Fintype VestaG]
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
      (fun index : Fin inputs.length => inputs[index.val]) witness)
    (hpositive : 0 < inputs.length) (hW : W ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let real := actionOracleProver urs rfl (fun index : Fin inputs.length => inputs[index.val]) witness vkTranscriptRepr cache
    let simulated := storedActionOracleBitSimulator fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U vkTranscriptRepr cache
    PMFEventBiasLE real simulated (plonkBitSimulationErrorBound inputs.length cache.length) ∧
      PMFEventBiasLE simulated real (plonkBitSimulationErrorBound inputs.length cache.length) := by
  dsimp only
  rw [storedActionOracleBitSimulator_law]
  exact actionOracleBit_simulation_error_bound
    ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
    (fun index : Fin inputs.length => inputs[index.val]) witness hvalid hpositive hW vkTranscriptRepr cache

end Zcash.Snark.ZeroKnowledge
