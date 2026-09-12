import Zcash.Snark.ZeroKnowledge.PublicOpeningPointsCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!
# Counted public-group commitment folding

The input member list is constructed by the counted public-row and emitted-point
algorithms. The final fold charges every stored point and every challenge access,
group scaling, and addition. Its erasure is the actual first opening commitment.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The fully constructed first-group point list has the original exact length. -/
theorem firstPublicOpeningPointsCosted_length (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (firstPublicOpeningPointsCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x points).1.length = 4 * actions + 46 := by
  unfold firstPublicOpeningPointsCosted
  exact firstOpeningGroupCosted_length _ _ _ _ _ _

/-- Construct and fold every commitment in the public opening group. -/
def firstPublicOpeningCommitmentCosted (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) : G × ℕ :=
  let members := firstPublicOpeningPointsCosted costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x points
  let value := foldlCosted (fun state point =>
    (x1.1 • state + point, x1.2 + groupScale + groupAdd + 2)) members.1 (0, 1)
  (value.1, members.2 + value.2 + 1)

/-- Erasure is the original first collapsed group commitment for these exact rows and setup. -/
theorem firstPublicOpeningCommitmentCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (U : G)
    (x x1 : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (firstPublicOpeningCommitmentCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points).1 =
      plonkPublicGroupCommitments
        { k := 11, g := fun index => (generators index).1, w := W.1, u := U }
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 x1.1 (fun index => (points index).1) 0 := by
  simp only [firstPublicOpeningCommitmentCosted, foldlCosted_result,
    firstPublicOpeningPointsCosted_result costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W U x points,
    plonkPublicGroupCommitments, commitmentHornerFold]

/-- The first commitment's full budget includes all member construction and the final group fold. -/
theorem firstPublicOpeningCommitmentCosted_cost_le (costs : FieldOperationCosts)
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
    (firstPublicOpeningCommitmentCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points).2 ≤
      actions * actions + actions * (4 * access + 40) + 50 * access + 1200 +
        (4 * actions + 46) * (x1.2 + groupScale + groupAdd + 3) + 3 := by
  let members := firstPublicOpeningPointsCosted costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x points
  let step := fun (state point : G) => (x1.1 • state + point, x1.2 + groupScale + groupAdd + 2)
  have hfold := foldlCosted_cost_le_sum step members.1 (0, 1) (fun _ => True)
    (fun _ => x1.2 + groupScale + groupAdd + 2)
    trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => le_rfl)
  have hlength : members.1.length = 4 * actions + 46 :=
    firstPublicOpeningPointsCosted_length costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x points
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, hlength] at hfold
  have hmembers := firstPublicOpeningPointsCosted_cost_le costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x points rowRead generatorRead pointRead
    hinstances hfixed hsigma hgenerators hpoints
  dsimp only
  change members.2 + (foldlCosted step members.1 (0, 1)).2 + 1 ≤ _
  nlinarith

end Zcash.Snark.ZeroKnowledge
