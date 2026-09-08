import Zcash.Snark.ZeroKnowledge.ActionInstantiation

/-!
# Retry rates for the closed Action reference construction

The canonical encoded observer retries only a fresh-randomness request. Its rate
is bounded by the already proved failure budget. The Action simulation theorem
then supplies the simulator's retry bound, without reopening compiler premises.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open scoped ENNReal

variable [Fintype VestaG]

/-- A canonical Action retry is one of the failures covered by the reference bound. -/
theorem wideActionZk_retry_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hW : urs.w ≠ 0) :
    (actionZkProver urs hk inputs witness).toOuterMeasure plonkObservedRetrySet ≤
      plonkAttemptFailureBound actions := by
  have hsub : plonkObservedRetrySet ⊆
      {view : Challenges urs.k Fp × ProverAttemptResult | view.2.status ≠ .complete} := by
    intro view hr hc
    change view.2.status = .failed .retryRandomness at hr
    rw [hr] at hc
    cases hc
  exact ((actionZkProver urs hk inputs witness).toOuterMeasure.mono hsub).trans
    (wideVestaPlonkReferenceAttempt_failure_le urs hk _ _ witness hW)

/-- The witness-free Action simulator has the common failure budget as its retry bound. -/
theorem wideActionZkSimulator_retry_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0) :
    (actionZkSimulator urs hk inputs).toOuterMeasure plonkObservedRetrySet ≤
      plonkCommonFailureBound actions := by
  have h := (wideActionZkRelation_simulation_error_bound urs hk inputs witness hvalid hW).2
    plonkObservedRetrySet
  exact h.trans (add_le_add (wideActionZk_retry_le urs hk inputs witness hW) le_rfl)

/-- The common numerical condition guarantees a strictly positive real stopping probability. -/
theorem actionZkProver_retry_lt_one {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hW : urs.w ≠ 0) (hbudget : plonkCommonFailureBound actions < 1) :
    (actionZkProver urs hk inputs witness).toOuterMeasure plonkObservedRetrySet < 1 :=
  (wideActionZk_retry_le urs hk inputs witness hW).trans_lt
    ((show plonkAttemptFailureBound actions ≤ plonkCommonFailureBound actions from le_self_add).trans_lt hbudget)

/-- On every valid public statement, the same numerical condition normalizes the public simulator's retries. -/
theorem actionZkSimulator_retry_lt_one {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (hbudget : plonkCommonFailureBound actions < 1) :
    (actionZkSimulator urs hk inputs).toOuterMeasure plonkObservedRetrySet < 1 :=
  (wideActionZkSimulator_retry_le urs hk inputs witness hvalid hW).trans_lt hbudget

end Zcash.Snark.ZeroKnowledge
