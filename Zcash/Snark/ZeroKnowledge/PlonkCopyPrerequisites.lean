import Zcash.Snark.ZeroKnowledge.PlonkCopyWitness
import Zcash.Snark.ZeroKnowledge.PlonkReferenceRowLaw

/-!
# Removing copy products from the remaining row failure event

With original witness copy equations and public sigma coherence, the computed copy
identity holds for every challenge and row tape. The remaining prerequisite event
therefore contains only failed construction or gate division. This does not yet bound
that probability, assert perfect completeness, or simulate actual failed transcripts.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly.CPolynomial
open scoped ENNReal

/-- Valid original copies leave only construction and gates among the row prerequisites. -/
theorem plonkRowPrerequisites_iff_of_copy {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    PlonkRowPrerequisites vk pub witness ch tape ↔
      (plonkColumnAttempt vk pub witness ch tape).complete = true ∧
        ∀ a : Fin actions,
          ∀ poly ∈ (plonkConstraintModel vk pub ch (plonkTotalColumnRows vk pub witness ch tape)).gateConstraints a,
            (X ^ 2048 - 1 : CPoly) ∣ poly := by
  constructor
  · intro h
    exact ⟨h.complete, h.gates⟩
  · rintro ⟨hcomplete, hgates⟩
    exact ⟨hcomplete, hgates, plonkTotalColumnRows_copyProduct vk pub witness copies hcopy ch tape⟩

/-- Failure of construction or masked gates under the existing reference row experiment. -/
noncomputable def plonkGateConstructionFailureMass {actions k : ℕ} {G : Type*} [Zero G]
    (law : PMF (Challenges k Fp)) (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) : ℝ≥0∞ :=
  (plonkReferenceRowTapeLaw actions law).toOuterMeasure {state |
    ¬ ((plonkColumnAttempt vk pub witness state.1 state.2).complete = true ∧
      ∀ a : Fin actions,
        ∀ poly ∈ (plonkConstraintModel vk pub state.1
          (plonkTotalColumnRows vk pub witness state.1 state.2)).gateConstraints a,
          (X ^ 2048 - 1 : CPoly) ∣ poly)}

/-- The old prerequisite mass equals the construction-and-gate mass, without conditioning on success. -/
theorem plonkRowPrerequisiteFailureMass_eq_of_copy {actions k : ℕ} {G : Type*} [Zero G]
    (law : PMF (Challenges k Fp)) (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) :
    plonkRowPrerequisiteFailureMass law vk pub witness = plonkGateConstructionFailureMass law vk pub witness := by
  unfold plonkRowPrerequisiteFailureMass plonkGateConstructionFailureMass
  apply congrArg (fun event => (plonkReferenceRowTapeLaw actions law).toOuterMeasure event)
  ext state
  exact not_congr (plonkRowPrerequisites_iff_of_copy vk pub witness copies hcopy state.1 state.2)

end Zcash.Snark.ZeroKnowledge
