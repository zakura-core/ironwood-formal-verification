import Zcash.Snark.ZeroKnowledge.PlonkLookupCompletion
import Zcash.Snark.ZeroKnowledge.PlonkCopyPrerequisites

/-!
# Original valid rows discharge the remaining reference row event

Original gates and lookup tuple membership, together with the public expression
mask profile, imply construction completion and gate division on every tape. Their
failure mass is therefore zero under any challenge law. Original copy equations and
public sigma coherence then supply all row prerequisites. This does not assert full
proof acceptance: zero denominators and other protocol exceptions are still accounted
for separately, and the public circuit profiles still require concrete instantiation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly.CPolynomial
open scoped ENNReal

/-- Original valid advice and the public mask profile discharge construction and masked gates pointwise. -/
theorem plonkGateConstructionReady_of_original {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (ch : Challenges k Fp) (tape : Fin (126 * actions) → Fp) :
    (plonkColumnAttempt vk pub witness ch tape).complete = true ∧
      ∀ a : Fin actions,
        ∀ poly ∈ (plonkConstraintModel vk pub ch (plonkTotalColumnRows vk pub witness ch tape)).gateConstraints a,
          (X ^ 2048 - 1 : CPoly) ∣ poly :=
  ⟨plonkColumnAttempt_complete_of_original vk pub witness profile hvalid ch tape,
    plonkTotalColumnRows_gateConstraints_dvd vk pub witness profile hvalid ch tape⟩

/-- The explicit construction-and-gate failure mass vanishes for original valid advice and a public mask profile. -/
theorem plonkGateConstructionFailureMass_eq_zero {actions k : ℕ} {G : Type*} [Zero G]
    (law : PMF (Challenges k Fp)) (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness) :
    plonkGateConstructionFailureMass law vk pub witness = 0 := by
  unfold plonkGateConstructionFailureMass
  have hempty : {state : PlonkReferenceRowTape actions k |
      ¬ ((plonkColumnAttempt vk pub witness state.1 state.2).complete = true ∧
        ∀ a : Fin actions,
          ∀ poly ∈ (plonkConstraintModel vk pub state.1
            (plonkTotalColumnRows vk pub witness state.1 state.2)).gateConstraints a,
            (X ^ 2048 - 1 : CPoly) ∣ poly)} = ∅ := by
    ext state
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact plonkGateConstructionReady_of_original vk pub witness profile hvalid state.1 state.2
  rw [hempty, MeasureTheory.measure_empty]

/-- The original gate, lookup, and copy conditions supply every reference row prerequisite. -/
theorem plonkRowPrerequisites_of_original {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    PlonkRowPrerequisites vk pub witness ch tape :=
  (plonkRowPrerequisites_iff_of_copy vk pub witness copies hcopy ch tape).mpr
    (plonkGateConstructionReady_of_original vk pub witness profile hvalid ch tape)

/-- All residual row prerequisites have probability zero; denominator exceptions remain separate. -/
theorem plonkRowPrerequisiteFailureMass_eq_zero {actions k : ℕ} {G : Type*} [Zero G]
    (law : PMF (Challenges k Fp)) (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) :
    plonkRowPrerequisiteFailureMass law vk pub witness = 0 := by
  rw [plonkRowPrerequisiteFailureMass_eq_of_copy law vk pub witness copies hcopy]
  exact plonkGateConstructionFailureMass_eq_zero law vk pub witness profile hvalid

end Zcash.Snark.ZeroKnowledge
