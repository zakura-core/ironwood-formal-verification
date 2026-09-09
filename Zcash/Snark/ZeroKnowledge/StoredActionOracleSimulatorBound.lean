import Zcash.Snark.ZeroKnowledge.StoredActionOracleSimulatorCost
import Zcash.Snark.ZeroKnowledge.StoredActionOracleViewBound

/-! # A fixed complete runtime envelope for the original stored-input simulator -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- Complete initialization, bit-driven view, and cache programming under explicit primitive prices. -/
def storedActionOracleSimulatorCostBudget (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions bitLength cached : ℕ) (key : StoredPlonkKey) : ℕ :=
  let initial := actions * (storedActionInstanceCommitmentBudget fieldCosts
    ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess actions + 7) + actions * actions + read + 5
  let view := storedActionOracleViewCostBudget fieldCosts ipaCosts node equal read omegaAccess actions bitLength
    (actions + 1) key
  let programming := 22 * ((cached + 22) * (9490 * actions + 14207) + 4) + 2
  initial + view + programming + 4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Every complete stored tape obeys the same total bound, with all proof, query, and failure work retained. -/
theorem storedActionOracleSimulatorCosted_cost_le_fixed
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (bits : Fin (actionOracleSimulatorBitCount inputs.length 11) → Bool) :
    (storedActionOracleSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      vkTranscriptRepr cache (List.ofFn bits)).2 ≤
      storedActionOracleSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
        (actionOracleSimulatorBitCount inputs.length 11) cache.length (StoredPlonkKey.encode vk) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let publicInputs := fun index : Fin inputs.length => inputs[index.val]
  let pub := plonkPublicPolynomialsFromRows (actionInstanceRows publicInputs) fixed sigma
  let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  let proof := plonkVerifierSimulatorFromTape urs vk pub ch (reduceFieldTape parts.2)
  let initial := storedActionInitialCosted fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
    inputs setup (vkTranscriptRepr, read + 1)
  let view := storedActionOracleViewCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup
    (StoredPlonkKey.encode vk) (List.ofFn bits) initial.1
  have hiResult : initial.1 = actionOracleInitial urs vkTranscriptRepr publicInputs :=
    storedActionInitialCosted_result fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
      inputs generators W U fixed sigma (vkTranscriptRepr, read + 1)
  have hiLength : initial.1.length = inputs.length + 1 :=
    storedActionInitialCosted_length fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
      inputs setup (vkTranscriptRepr, read + 1)
  have hi : initial.2 ≤ inputs.length * (storedActionInstanceCommitmentBudget fieldCosts
      ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess inputs.length + 7) +
      inputs.length * inputs.length + read + 5 := by
    have h := storedActionInitialCosted_cost_le fieldCosts ipaCosts.groupAdd ipaCosts.groupScale read omegaAccess
      inputs generators W U fixed sigma (vkTranscriptRepr, read + 1)
    exact h.trans (by omega)
  have hv := storedActionOracleViewCosted_cost_le_fixed fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma vk bits initial.1
  conv at hv =>
    rhs
    rw [hiLength]
  change view.2 ≤ storedActionOracleViewCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
    (actionOracleSimulatorBitCount inputs.length 11) (inputs.length + 1) (StoredPlonkKey.encode vk) at hv
  have hvResult : view.1 = plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr publicInputs) parts.1 proof := by
    have h := storedActionOracleViewCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U fixed sigma vk bits initial.1
    dsimp only at h
    conv at h =>
      rhs
      rw [hiResult]
    exact h
  have hp : (programOracleViewCosted cache view.1).2 ≤
      22 * ((cache.length + 22) * (9490 * inputs.length + 14207) + 4) + 2 := by
    rw [hvResult]
    exact actionOracleView_programming_cost_le urs rfl publicInputs vkTranscriptRepr cache parts.1 proof
  change initial.2 + view.2 + (programOracleViewCosted cache view.1).2 + 4 ≤ _
  dsimp only [storedActionOracleSimulatorCostBudget]
  omega

end Zcash.Snark.ZeroKnowledge
