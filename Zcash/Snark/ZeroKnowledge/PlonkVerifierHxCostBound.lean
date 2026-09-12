import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCostBound
import Zcash.Snark.ZeroKnowledge.PlonkConstraintListLength

/-!
# Complete inferred quotient cost bound

The bound includes domain powering, every Lagrange value, full claim and
constraint preparation, output materialization, and the final quotient fold.
It holds for all field values, including a zero vanishing denominator.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- The complete quotient budget, polynomial in the Action count and actual stored key sizes. -/
def plonkVerifierHxCostBudget (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    (actions viewCount access xAccess yAccess : ℕ) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (n blinding stride : ℕ) : ℕ :=
  let length := actions * (gates.1.length + 23)
  xAccess + (n * (costs.multiply + 1) + 1) +
    ((blinding + 2) * lagrangeBasisValueCostBudget costs n (blinding + 1) access +
      blinding * (costs.add + 1) + blinding * blinding + 2) +
    plonkClaimConstraintsCostBudget costs node equal read omegaAccess actions viewCount access xAccess
      gates layout inputs tables stride + (length * 3 + 1) +
    (length * (yAccess + 1 + costs.multiply + costs.add + 2) +
      1 + costs.add + costs.negate + costs.multiply + costs.inverse + 8) + 1

/-- Every operation and input preparation in the existing quotient computation fits the stated budget. -/
theorem plonkVerifierHxCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (omega : Fp × ℕ) (n blinding : ℕ) (beta gamma x y delta theta : Fp × ℕ) (stride : ℕ)
    (access : ℕ) (hunit : 1 ≤ access)
    (hinstances : ∀ action row, (instances action row).2 ≤ access)
    (hfixed : ∀ column row, (fixed column row).2 ≤ access)
    (hsigma : ∀ column row, (sigma column row).2 ≤ access)
    (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access)
    (hinputs : ∀ index, (inputs index).2 ≤ access) (htables : ∀ index, (tables index).2 ≤ access)
    (homega : omega.2 ≤ access) (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access)
    (hx : x.2 ≤ access) (hdelta : delta.2 ≤ access) (htheta : theta.2 ≤ access) :
    (plonkVerifierHxCosted costs node equal read omegaAccess instances fixed sigma views gates layout
      inputs tables omega n blinding beta gamma x y delta theta stride).2 ≤
      plonkVerifierHxCostBudget costs node equal read omegaAccess actions views.length access x.2 y.2
        gates layout inputs tables n blinding stride := by
  let power := fieldPowerCosted costs.multiply x.1 n
  let basis := lagrangeBasisCosted costs omega n blinding (power.1, 1) x
  let constraints := plonkClaimConstraintsCosted costs node equal read omegaAccess
    instances fixed sigma views gates layout inputs tables beta gamma x delta theta stride
    (basis.1.1, 1) (basis.1.2.1, 1) (basis.1.2.2, 1)
  let entries := mapListCosted (fun value => ((value, 1), 2)) constraints.1
  let result := expectedHEvalCosted costs entries.1 y (power.1, 1)
  let length := actions * (gates.1.length + 23)
  have hpower := fieldPowerCosted_cost costs.multiply x.1 n
  have hbasis := lagrangeBasisCosted_cost_le costs omega n blinding (power.1, 1) x access homega hunit hx
  have hconstraints := plonkClaimConstraintsCosted_cost_le costs node equal read omegaAccess
    instances fixed sigma views gates layout inputs tables beta gamma x delta theta stride
    (basis.1.1, 1) (basis.1.2.1, 1) (basis.1.2.2, 1) access
    hinstances hfixed hsigma hviews hinputs htables hbeta hgamma hx hdelta htheta hunit hunit hunit
  have hlength := plonkClaimConstraintsCosted_length_le costs node equal read omegaAccess
    instances fixed sigma views gates layout inputs tables beta gamma x delta theta stride
    (basis.1.1, 1) (basis.1.2.1, 1) (basis.1.2.2, 1)
  change constraints.1.length ≤ length at hlength
  have hentries := mapListCosted_cost_le (fun value : Fp => ((value, 1), 2)) constraints.1 2
    (fun _ _ => le_rfl)
  change entries.2 ≤ constraints.1.length * 3 + 1 at hentries
  have hentriesLength : entries.1.length ≤ length := by
    simpa only [entries, mapListCosted_result, List.length_map] using hlength
  have hread : ∀ value ∈ entries.1, value.2 ≤ 1 := by
    intro value hmem
    simp only [entries, mapListCosted_result, List.mem_map] at hmem
    obtain ⟨_, _, rfl⟩ := hmem
    exact le_rfl
  have hresult := expectedHEvalCosted_cost_le costs entries.1 y (power.1, 1) 1 hread
  have hentriesScale := Nat.mul_le_mul_right 3 hlength
  have hresultScale := Nat.mul_le_mul_right (y.2 + 1 + costs.multiply + costs.add + 2) hentriesLength
  change power.2 = _ at hpower
  change basis.2 ≤ _ at hbasis
  change constraints.2 ≤ _ at hconstraints
  change result.2 ≤ entries.1.length * (y.2 + 1 + costs.multiply + costs.add + 2) +
    1 + costs.add + costs.negate + costs.multiply + costs.inverse + 8 at hresult
  change x.2 + power.2 + basis.2 + constraints.2 + entries.2 + result.2 + 1 ≤ _
  dsimp only [plonkVerifierHxCostBudget]
  change _ ≤ x.2 + (n * (costs.multiply + 1) + 1) +
    ((blinding + 2) * lagrangeBasisValueCostBudget costs n (blinding + 1) access +
      blinding * (costs.add + 1) + blinding * blinding + 2) +
    plonkClaimConstraintsCostBudget costs node equal read omegaAccess actions views.length access x.2
      gates layout inputs tables stride + (length * 3 + 1) +
    (length * (y.2 + 1 + costs.multiply + costs.add + 2) +
      1 + costs.add + costs.negate + costs.multiply + costs.inverse + 8) + 1
  omega

end Zcash.Snark.ZeroKnowledge
