import Zcash.Snark.ZeroKnowledge.PlonkSimulatorAcceptance
import Zcash.Snark.ZeroKnowledge.PlonkCompletenessBounds

/-!
# From statistical simulation to prover completeness

Acceptance requires both completion of the actual emission schedule and
`DeployedAccepts` for the same typed proof and received challenges. The theorem
transfers the simulator's proved rejection bound to the real prover, then adds
the honest emission-failure bound. Its simulation premise is discharged for
valid Action witnesses in `ActionProverCompleteness`.

The bound is deliberately conservative: exceptional challenges already charged
in the simulation comparison are also charged when proving simulator acceptance.
It is an unconditional one-attempt bound, with aborts and rejections retained.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS omegaOf)
open Zcash.Common
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G]

/-- A completed emission whose typed proof is accepted by the complete rejecting verifier. -/
def plonkAcceptedAttemptSet {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (instanceCommitment : Fin actions → ℕ → G)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    Set (PlonkFreshView actions urs.k G) :=
  plonkAttemptSuccessSet pointCodec scalarCodec ∩
    {view | DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk
      instanceCommitment view.2 view.1}

/-- A proved simulation comparison bounds abort or verifier rejection of the same reference prover. -/
theorem widePlonk_completeness_error_bound [Fintype G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hpositive : 0 < actions)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11)
    (hW : Function.Bijective (fun r : Fp => r • urs.w))
    (hsimulation : PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub)
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (plonkSimulationErrorBound actions)) :
    (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub).toOuterMeasure
        (plonkAcceptedAttemptSet urs vk instanceCommitment pointCodec scalarCodec)ᶜ ≤
      plonkCompletenessErrorBound actions := by
  let actual := freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub
  let rejection : Set (PlonkFreshView actions urs.k G) :=
    {view | ¬ DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk
      instanceCommitment view.2 view.1}
  have hsimulator :
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).toOuterMeasure
        rejection ≤ plonkVerifierRejectionBound := by
    have h := widePlonkVerifierSimulator_rejection_prob_le urs vk hlayout pub
      instanceCommitment hpositive hpublic hn homega
    have hcount :
        (((urs.k + 4102 : ℕ) : ℝ≥0∞) / Zcash.Arithmetic.scalarFieldOrder) +
          (((urs.k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) = plonkVerifierRejectionBound := by
      rw [hk]
      rfl
    exact h.trans_eq hcount
  have hreject : actual.toOuterMeasure rejection ≤
      plonkVerifierRejectionBound + plonkSimulationErrorBound actions :=
    event_measure_le_of_bias hsimulation rejection hsimulator
  have habort : actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      plonkAttemptFailureBound actions :=
    widePlonkAttempt_failure_le urs hk construct history vk pub pointCodec scalarCodec hcodec hW
  change actual.toOuterMeasure _ ≤ _
  rw [plonkAcceptedAttemptSet, Set.compl_inter]
  calc
    _ ≤ actual.toOuterMeasure (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ +
        actual.toOuterMeasure rejection := MeasureTheory.measure_union_le _ _
    _ ≤ plonkAttemptFailureBound actions +
        (plonkVerifierRejectionBound + plonkSimulationErrorBound actions) :=
      add_le_add habort hreject
    _ = _ := by
      unfold plonkCompletenessErrorBound
      ac_rfl

end Zcash.Snark.ZeroKnowledge
