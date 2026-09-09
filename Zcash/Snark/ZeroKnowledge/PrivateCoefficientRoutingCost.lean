import Zcash.Snark.ZeroKnowledge.PrivatePolynomialCoefficientsCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Route a stored private polynomial through the actual column schedule and defaulted list read. -/
def privateColumnCoefficientsCosted {actions : ℕ} (equal read : ℕ)
    (polys : List (List Fp)) (id : PrivateColumnId actions) : List Fp × ℕ :=
  let index := privateColumnIndexCosted equal id
  let result := getDListCosted read [] polys index.1
  (result.1, index.2 + result.2 + 1)

/-- Erasure selects the original column position, with the original zero-polynomial default. -/
theorem privateColumnCoefficientsCosted_result {actions : ℕ} (equal read : ℕ)
    (polys : List (List Fp)) (id : PrivateColumnId actions) :
    densePolynomial (privateColumnCoefficientsCosted equal read polys id).1 =
      (polys.map densePolynomial).getD ((privateColumnOrder actions).idxOf id) 0 := by
  simp only [privateColumnCoefficientsCosted, getDListCosted_result, privateColumnIndexCosted_result,
    privateColumnIndex, densePolynomial_getD]

/-- Every routed polynomial fits the stored input capacity, including a missing column. -/
theorem privateColumnCoefficientsCosted_length_le {actions : ℕ} (equal read : ℕ)
    (polys : List (List Fp)) (id : PrivateColumnId actions) (width : ℕ)
    (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (privateColumnCoefficientsCosted equal read polys id).1.length ≤ width :=
  getDListCosted_property read [] polys (fun poly => poly.length ≤ width)
    (Nat.zero_le _) hpolys (privateColumnIndexCosted equal id).1

/-- Complete identifier construction, equality search, and stored polynomial access budget. -/
def privateColumnCoefficientsCostBudget (equal read actions columns : ℕ) : ℕ :=
  4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + 2 * columns + read + 14

/-- Routing counts all source-list traversal and construction work. -/
theorem privateColumnCoefficientsCosted_cost_le {actions : ℕ} (equal read : ℕ)
    (polys : List (List Fp)) (id : PrivateColumnId actions) :
    (privateColumnCoefficientsCosted equal read polys id).2 ≤
      privateColumnCoefficientsCostBudget equal read actions polys.length := by
  have hi := privateColumnIndexCosted_cost_le equal id
  have hr := getDListCosted_cost_le read [] polys (privateColumnIndexCosted equal id).1
  change _ + _ + 1 ≤ _
  unfold privateColumnCoefficientsCostBudget
  omega

/-- A routed coefficient vector constructed from rows denotes precisely the reference private column. -/
theorem privateColumnCoefficientsCosted_from_rows (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ} (rows : List (Fin 2048 → Fp × ℕ))
    (id : PrivateColumnId actions) :
    densePolynomial (privateColumnCoefficientsCosted equal read
      (privatePolynomialCoefficientsCosted costs (Zcash.Arithmetic.omegaOf 11, omegaAccess) rows).1 id).1 =
      privateColumnPolynomial (rows.map (fun column row => (column row).1)) id := by
  rewrite [privateColumnCoefficientsCosted_result,
    privatePolynomialCoefficientsCosted_result costs 11 (by decide) omegaAccess]
  simp only [privateColumnPolynomial, List.map_map, Function.comp_def]
  rfl

end Zcash.Snark.ZeroKnowledge
