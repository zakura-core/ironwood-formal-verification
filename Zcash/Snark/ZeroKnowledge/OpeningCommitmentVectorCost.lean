import Zcash.Snark.ZeroKnowledge.PublicOpeningCommitmentCost
import Zcash.Snark.ZeroKnowledge.PrivateOpeningPointCost

/-!
# Counted reconstruction of all five opening commitments

The first group constructs and folds its public row commitments and emitted
points. The remaining four groups use the counted private member folds. Every
output point is materialized, and all preparation remains in the total cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Reconstruct and materialize all five original opening commitments. -/
def openingCommitmentVectorCosted (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) : List G × ℕ :=
  let first := firstPublicOpeningCommitmentCosted costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x x1 points
  let rest := ofFnCosted (privateOpeningPointCosted groupAdd groupScale equal points x1)
  (first.1 :: rest.1, first.2 + rest.2 + 2)

/-- Every materialized group is exactly the reference verifier's reconstructed commitment. -/
theorem openingCommitmentVectorCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (U : G)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (openingCommitmentVectorCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points).1 =
      List.ofFn (plonkPublicGroupCommitments
        { k := 11, g := fun index => (generators index).1, w := W.1, u := U }
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 x1.1 (fun index => (points index).1)) := by
  conv_rhs => rw [List.ofFn_succ]
  simp only [openingCommitmentVectorCosted, ofFnCosted_result,
    firstPublicOpeningCommitmentCosted_result costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W U x x1 points]
  congr 1
  congr 1
  funext group
  simp only [privateOpeningPointCosted_result, plonkPublicGroupCommitments,
    plonkPublicCommitmentMembers, Fin.cons_succ]

/-- All five commitments are materialized before later multi-opening or encoding work. -/
theorem openingCommitmentVectorCosted_length (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (openingCommitmentVectorCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points).1.length = 5 := by
  simp only [openingCommitmentVectorCosted, List.length_cons, ofFnCosted_length]

/-- The entire commitment-vector bound includes all public and private group preparation. -/
theorem openingCommitmentVectorCosted_cost_le (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ)
    (rowRead generatorRead pointRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hgenerators : ∀ index, (generators index).2 ≤ generatorRead)
    (hpoints : ∀ index, (points index).2 ≤ pointRead) :
    let access := publicOpeningPointAccessBudget costs groupAdd groupScale equal omegaAccess actions
      rowRead generatorRead W.2 pointRead x.2
    let firstBudget := actions * actions + actions * (4 * access + 40) + 50 * access + 1200 +
      (4 * actions + 46) * (x1.2 + groupScale + groupAdd + 3) + 3
    let privateBudget := actions * actions + 35 * actions + 9 * actions *
      (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + pointRead + 13 +
        x1.2 + groupScale + groupAdd + 2) + 4
    (openingCommitmentVectorCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points).2 ≤ firstBudget + 4 * (privateBudget + 1) + 19 := by
  have hfirst := firstPublicOpeningCommitmentCosted_cost_le costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x x1 points rowRead generatorRead pointRead
    hinstances hfixed hsigma hgenerators hpoints
  have hrest := ofFnCosted_cost_le (privateOpeningPointCosted groupAdd groupScale equal points x1)
    _ (fun group => privateOpeningPointCosted_cost_le groupAdd groupScale equal points x1 group pointRead hpoints)
  dsimp only
  simp only [openingCommitmentVectorCosted]
  omega

end Zcash.Snark.ZeroKnowledge
