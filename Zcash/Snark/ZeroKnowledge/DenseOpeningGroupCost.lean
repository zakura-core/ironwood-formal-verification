import Zcash.Snark.ZeroKnowledge.PrivateCoefficientRoutingCost
import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutProperties
import Zcash.Snark.ZeroKnowledge.QueryOrderCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Route the actual fixed-query order, retaining the selected provider's complete cost. -/
def fixedCoefficientQueryCosted (fixed : Fin 29 → List Fp × ℕ) (query : Fin 29) : List Fp × ℕ :=
  let index := fixedQueryOrderCosted query
  let value := fixed index.1
  (value.1, index.2 + value.2 + 1)

/-- The routed coefficients are those of the source's fixed-query entry. -/
theorem fixedCoefficientQueryCosted_result (fixed : Fin 29 → List Fp × ℕ) (query : Fin 29) :
    (fixedCoefficientQueryCosted fixed query).1 = (fixed (plonkFixedQueryOrder query)).1 := by
  simp only [fixedCoefficientQueryCosted, fixedQueryOrderCosted_result]

/-- Query-table construction and the selected polynomial producer are both counted. -/
theorem fixedCoefficientQueryCosted_cost_le (fixed : Fin 29 → List Fp × ℕ) (query : Fin 29)
    (access : ℕ) (hfixed : ∀ index, (fixed index).2 ≤ access) :
    (fixedCoefficientQueryCosted fixed query).2 ≤ access + 120 := by
  have hi := fixedQueryOrderCosted_cost_le query
  have hv := hfixed (fixedQueryOrderCosted query).1
  change _ + _ + 1 ≤ _
  omega

/-- Materialize an actual opening group's stored polynomials in the original source order. -/
def denseOpeningGroupMembersCosted (equal read : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (group : Fin 5) : List (List Fp) × ℕ :=
  Fin.cases
    (firstOpeningGroupCosted instances
      (fun action lookup => privateColumnCoefficientsCosted equal read columns (.lookupTable action lookup))
      (fixedCoefficientQueryCosted fixed) sigma quotient linear)
    (fun index =>
      let members := privateOpeningGroupCosted actions index
      let result := mapListCosted (privateColumnCoefficientsCosted equal read columns) members.1
      (result.1, members.2 + result.2 + 1)) group

/-- Supplied coefficient semantics identify the complete original group, including all defaults and mask placement. -/
theorem denseOpeningGroupMembersCosted_result (equal read : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hinstances : ∀ action, densePolynomial (instances action).1 = pub.instances action)
    (hfixed : ∀ index, densePolynomial (fixed index).1 = pub.fixed index)
    (hsigma : ∀ index, densePolynomial (sigma index).1 = pub.sigma index)
    (hcolumns : ∀ id : PrivateColumnId actions,
      densePolynomial (privateColumnCoefficientsCosted equal read columns id).1 = privateColumnPolynomial rows id)
    (hquotient : densePolynomial quotient.1 = plonkCollapsedQuotient x pieces)
    (hlinear : densePolynomial linear.1 = linearMaskPolynomial coefficients) (group : Fin 5) :
    ((denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1.map densePolynomial) =
      plonkOpeningGroups pub rows x pieces coefficients group := by
  refine Fin.cases ?_ (fun index => ?_) group
  · simp only [denseOpeningGroupMembersCosted, Fin.cases_zero, firstOpeningGroupCosted_result,
      List.map_append, List.map_flatMap, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      fixedCoefficientQueryCosted_result, hinstances, hfixed, hsigma, hcolumns, hquotient, hlinear,
      plonkOpeningGroups, Fin.cons_zero, plonkFirstGroupPrefix, List.append_assoc, List.singleton_append]
  · simp only [denseOpeningGroupMembersCosted, Fin.cases_succ, mapListCosted_result,
      privateOpeningGroupCosted_result, List.map_map, Function.comp_def, hcolumns,
      plonkOpeningGroups, Fin.cons_succ]

/-- Every opening group contains at most nine entries per Action plus the fixed public suffix. -/
theorem denseOpeningGroupMembersCosted_length_le (equal read : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (group : Fin 5) :
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1.length ≤
      9 * actions + 46 := by
  refine Fin.cases ?_ (fun index => ?_) group
  · change (firstOpeningGroupCosted instances _ _ sigma quotient linear).1.length ≤ _
    rewrite [firstOpeningGroupCosted_length]
    omega
  · change (mapListCosted (privateColumnCoefficientsCosted equal read columns)
      (privateOpeningGroupCosted actions index).1).1.length ≤ _
    rewrite [mapListCosted_result, List.length_map]
    exact (privateOpeningGroupCosted_length_le actions index).trans (Nat.le_add_right _ _)

/-- Every selected member fits the common polynomial storage capacity. -/
theorem denseOpeningGroupMembersCosted_width (equal read : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (width : ℕ)
    (hinstances : ∀ action, (instances action).1.length ≤ width)
    (hfixed : ∀ index, (fixed index).1.length ≤ width)
    (hsigma : ∀ index, (sigma index).1.length ≤ width)
    (hcolumns : ∀ column ∈ columns, column.length ≤ width)
    (hquotient : quotient.1.length ≤ width) (hlinear : linear.1.length ≤ width) (group : Fin 5) :
    ∀ member ∈ (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1,
      member.length ≤ width := by
  refine Fin.cases ?_ (fun index => ?_) group
  · exact firstOpeningGroupCosted_property instances
      (fun action lookup => privateColumnCoefficientsCosted equal read columns (.lookupTable action lookup))
      (fixedCoefficientQueryCosted fixed) sigma quotient linear (fun poly => poly.length ≤ width)
      hinstances (fun action lookup => privateColumnCoefficientsCosted_length_le equal read columns
        (.lookupTable action lookup) width hcolumns)
      (fun query => by rewrite [fixedCoefficientQueryCosted_result]; exact hfixed _) hsigma hquotient hlinear
  · intro member hmember
    change member ∈ (mapListCosted (privateColumnCoefficientsCosted equal read columns)
      (privateOpeningGroupCosted actions index).1).1 at hmember
    simp only [mapListCosted_result, List.mem_map] at hmember
    obtain ⟨id, _, rfl⟩ := hmember
    exact privateColumnCoefficientsCosted_length_le equal read columns id width hcolumns

/-- Complete layout and routing envelope for either kind of opening group. -/
def denseOpeningGroupMembersCostBudget (equal read actions columns access : ℕ) : ℕ :=
  let route := privateColumnCoefficientsCostBudget equal read actions columns
  let member := access + route + 120
  (actions * actions + actions * (4 * member + 40) + 50 * member + 1200) +
    (actions * actions + 35 * actions + 9 * actions * (route + 1) + 3)

/-- Every actual member producer, identifier, fixed query, and copied list cell is counted. -/
theorem denseOpeningGroupMembersCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (access : ℕ)
    (hinstances : ∀ action, (instances action).2 ≤ access)
    (hfixed : ∀ index, (fixed index).2 ≤ access) (hsigma : ∀ index, (sigma index).2 ≤ access)
    (hquotient : quotient.2 ≤ access) (hlinear : linear.2 ≤ access) (group : Fin 5) :
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).2 ≤
      denseOpeningGroupMembersCostBudget equal read actions columns.length access := by
  let route := privateColumnCoefficientsCostBudget equal read actions columns.length
  let member := access + route + 120
  refine Fin.cases ?_ (fun index => ?_) group
  · have h := firstOpeningGroupCosted_cost_le instances
      (fun action lookup => privateColumnCoefficientsCosted equal read columns (.lookupTable action lookup))
      (fixedCoefficientQueryCosted fixed) sigma quotient linear member
      (fun action => (hinstances action).trans (by dsimp [member]; omega))
      (fun action lookup => (privateColumnCoefficientsCosted_cost_le equal read columns (.lookupTable action lookup)).trans
        (by change route ≤ member; dsimp only [member]; omega))
      (fun query => (fixedCoefficientQueryCosted_cost_le fixed query access hfixed).trans (by dsimp only [member]; omega))
      (fun index => (hsigma index).trans (by dsimp only [member]; omega))
      (hquotient.trans (by dsimp only [member]; omega)) (hlinear.trans (by dsimp only [member]; omega))
    exact h.trans (Nat.le_add_right _ _)
  · have hm := privateOpeningGroupCosted_cost_le actions index
    have hl := privateOpeningGroupCosted_length_le actions index
    have hv := mapListCosted_cost_le (privateColumnCoefficientsCosted equal read columns)
      (privateOpeningGroupCosted actions index).1 route
      (fun id _ => privateColumnCoefficientsCosted_cost_le equal read columns id)
    have hh := Nat.mul_le_mul_right (route + 1) hl
    change (privateOpeningGroupCosted actions index).2 +
      (mapListCosted (privateColumnCoefficientsCosted equal read columns)
        (privateOpeningGroupCosted actions index).1).2 + 1 ≤ _
    change _ ≤ _ + (actions * actions + 35 * actions + 9 * actions * (route + 1) + 3)
    omega

end Zcash.Snark.ZeroKnowledge
