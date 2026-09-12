import Zcash.Snark.ZeroKnowledge.StoredPlonkOpeningGroupCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Materialize every original opening group, retaining its coefficients, points, and inherited blind. -/
def storedPlonkOpeningGroupsCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ)
    (x x1 : Fp × ℕ) : List StoredOpeningGroup × ℕ :=
  ofFnCosted (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1)

/-- Erasing the materialized records gives the original complete blinded-opening list. -/
theorem storedPlonkOpeningGroupsCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hpolynomials : polynomials.map densePolynomial = List.ofFn (plonkOpeningPolynomials pub rows x.1 x1.1 pieces coefficients)) :
    ((storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials entries x x1).1.map StoredOpeningGroup.erase) =
      plonkBlindedOpeningGroups pub rows x.1 x1.1 pieces coefficients
        (plonkCommitmentBlindsFromVector (fun index => (entries index).1)) := by
  simp only [storedPlonkOpeningGroupsCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    storedPlonkOpeningGroupCosted_result costs equal read omegaAccess polynomials entries x x1 pub rows pieces coefficients
      hpolynomials, plonkBlindedOpeningGroups]

/-- There are exactly five complete group records in source order. -/
theorem storedPlonkOpeningGroupsCosted_length (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ) :
    (storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials entries x x1).1.length = 5 :=
  ofFnCosted_length (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1)

/-- Every group preserves the common coefficient capacity and the actual one-to-three-node layout. -/
theorem storedPlonkOpeningGroupsCosted_dimensions (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (width : ℕ) (hpolynomials : ∀ poly ∈ polynomials, poly.length ≤ width)
    (group : StoredOpeningGroup)
    (hgroup : group ∈ (storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials entries x x1).1) :
    group.coefficients.length ≤ width ∧ 0 < group.points.length ∧ group.points.length ≤ 3 := by
  simp only [storedPlonkOpeningGroupsCosted, ofFnCosted_result, List.mem_ofFn] at hgroup
  obtain ⟨index, rfl⟩ := hgroup
  exact ⟨storedPlonkOpeningGroupCosted_width costs equal read omegaAccess polynomials entries x x1 width hpolynomials index,
    storedPlonkOpeningGroupCosted_points costs equal read omegaAccess polynomials entries x x1 index⟩

/-- The complete group vector charges all five providers, finite-index adapters, and output records. -/
theorem storedPlonkOpeningGroupsCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (access : ℕ) (hread : ∀ index, (entries index).2 ≤ access) :
    (storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials entries x x1).2 ≤
      5 * (storedPlonkOpeningGroupCostBudget costs equal read omegaAccess actions polynomials.length access x.2 x1.2 + 1) + 26 :=
  ofFnCosted_cost_le (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1)
    (storedPlonkOpeningGroupCostBudget costs equal read omegaAccess actions polynomials.length access x.2 x1.2)
    (storedPlonkOpeningGroupCosted_cost_le costs equal read omegaAccess polynomials entries x x1 access hread)

/-- Point capacities depend only on the original group layout, independently of coefficient storage. -/
theorem storedPlonkOpeningGroupsCosted_points (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (group : StoredOpeningGroup)
    (hgroup : group ∈ (storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials entries x x1).1) :
    0 < group.points.length ∧ group.points.length ≤ 3 := by
  simp only [storedPlonkOpeningGroupsCosted, ofFnCosted_result, List.mem_ofFn] at hgroup
  obtain ⟨index, rfl⟩ := hgroup
  exact storedPlonkOpeningGroupCosted_points costs equal read omegaAccess polynomials entries x x1 index

end Zcash.Snark.ZeroKnowledge
