import Zcash.Snark.ZeroKnowledge.ActionConstraintsRelation
import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionGateActivationCoverage
import Zcash.Snark.ZeroKnowledge.ActionLookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.ActionWitnessCompleteness
import Zcash.Snark.ZeroKnowledge.ActionOracleBits
import Zcash.Snark.ZeroKnowledge.StoredActionOracleRuntime

/-! # Statistical simulation for rows constructed from application Action witnesses -/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- The generated application assignment satisfies the complete original Action constraints. -/
theorem actionWitnessAssignment_constraints (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (conditions : ActionWitnessConstructionConditions inputs witness) :
    Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment inputs witness)) actionCircuit.operations 0 :=
  actionWitnessAssignment_constraints_of_extendsWitnesses inputs witness conditions
    (actionWitnessAssignment_extendsWitnesses inputs witness)

/-- Application witness conditions supply every original row and compiler copy premise. -/
theorem actionWitnessRows_relation {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action)) :
    ActionZkRelation urs hk inputs (actionWitnessRowBundle inputs witnesses) :=
  actionWitnessRows_relation_of_constraints urs hk inputs witnesses
    actionCircuit_gateActivationCoverage actionCircuit_lookupActivationCoverage
    (fun action => actionWitnessAssignment_constraints (inputs action) (witnesses action) (conditions action))

/-- Statistical simulation for the rows constructed from the application Action witnesses. -/
theorem wideActionWitness_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hW : urs.w ≠ 0) :
    PMFEventBiasLE (actionZkProver urs hk inputs (actionWitnessRowBundle inputs witnesses))
        (actionZkSimulator urs hk inputs) (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkSimulator urs hk inputs)
        (actionZkProver urs hk inputs (actionWitnessRowBundle inputs witnesses))
        (plonkSimulationErrorBound actions) :=
  wideActionZkRelation_simulation_error_bound urs hk inputs (actionWitnessRowBundle inputs witnesses)
    (actionWitnessRows_relation urs hk inputs witnesses conditions) hW

/-- The captured setup supplies its checked blinding-generator condition for application witnesses. -/
theorem wideCapturedActionWitness_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action)) :
    PMFEventBiasLE
        (actionZkProver capturedActionURS capturedActionURS_rounds inputs (actionWitnessRowBundle inputs witnesses))
        (actionZkSimulator capturedActionURS capturedActionURS_rounds inputs)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkSimulator capturedActionURS capturedActionURS_rounds inputs)
        (actionZkProver capturedActionURS capturedActionURS_rounds inputs (actionWitnessRowBundle inputs witnesses))
        (plonkSimulationErrorBound actions) :=
  wideActionWitness_simulation_error_bound capturedActionURS capturedActionURS_rounds inputs witnesses
    conditions capturedActionURS_blinding_ne_zero

/-- The same constructed rows instantiate the complete one-attempt fixed-bit oracle comparison. -/
theorem actionOracleBitWitness_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMFEventBiasLE
        (actionOracleProver urs hk inputs (actionWitnessRowBundle inputs witnesses) vkTranscriptRepr cache)
        (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache)
        (plonkBitSimulationErrorBound actions cache.length) ∧
      PMFEventBiasLE (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs (actionWitnessRowBundle inputs witnesses) vkTranscriptRepr cache)
        (plonkBitSimulationErrorBound actions cache.length) :=
  actionOracleBit_simulation_error_bound urs hk inputs (actionWitnessRowBundle inputs witnesses)
    (actionWitnessRows_relation urs hk inputs witnesses conditions) hpositive hW vkTranscriptRepr cache

/-- Application witnesses instantiate the same complete counted simulator and its statistical law. -/
theorem storedActionOracleBitWitness_simulation_error_bound [Fintype VestaG]
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witnesses : Fin inputs.length → PrivateWitness)
    (conditions : ∀ action : Fin inputs.length,
      ActionWitnessConstructionConditions inputs[action.val] (witnesses action))
    (hpositive : 0 < inputs.length) (hW : W ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let publicInputs := fun action : Fin inputs.length => inputs[action.val]
    let real := actionOracleProver urs rfl publicInputs (actionWitnessRowBundle publicInputs witnesses)
      vkTranscriptRepr cache
    let simulated := storedActionOracleBitSimulator fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U vkTranscriptRepr cache
    PMFEventBiasLE real simulated (plonkBitSimulationErrorBound inputs.length cache.length) ∧
      PMFEventBiasLE simulated real (plonkBitSimulationErrorBound inputs.length cache.length) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let publicInputs := fun action : Fin inputs.length => inputs[action.val]
  exact storedActionOracleBit_simulation_error_bound fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U (actionWitnessRowBundle publicInputs witnesses)
    (actionWitnessRows_relation urs rfl publicInputs witnesses conditions) hpositive hW vkTranscriptRepr cache

end Zcash.Snark.ZeroKnowledge
