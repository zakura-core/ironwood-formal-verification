import Zcash.Snark.ZeroKnowledge.KeygenExpressionDegree
import Zcash.Snark.ZeroKnowledge.SelectorCompressionDegree

/-!
# Degree accounting for packed selector replacements

Each root-finding replacement has degree at most its combination length. A weighted
source expression counts a selector at its permitted replacement degree, while
ordinary column queries retain degree one. The compiler's substitution is bounded
by this source calculation before expression erasure or query resolution.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

private theorem foldl_mul_degree_le {F : Type} (factors : List (Expression F Query))
    (accumulator : Expression F Query) (hlinear : ∀ factor ∈ factors, factor.degree ≤ 1) :
    (factors.foldl (· * ·) accumulator).degree ≤ accumulator.degree + factors.length := by
  induction factors generalizing accumulator with
  | nil => simp
  | cons factor rest ih =>
      rw [List.foldl_cons]
      have hrest := ih (accumulator * factor) (fun f hf => hlinear f (List.mem_cons_of_mem _ hf))
      have hfactor := hlinear factor List.mem_cons_self
      change _ ≤ accumulator.degree + (factor :: rest).length
      change _ ≤ accumulator.degree + factor.degree + rest.length at hrest
      simp only [List.length_cons]
      omega

/-- A valid assigned root removes one linear factor, so the replacement degree fits its combination length. -/
theorem selReplacement_degree_le {F : Type} [Field F] (compressed : SelCompress)
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hroot : compressed.assignedRoot ≤ compressed.combinationLen) :
    (selReplacement (F := F) compressed).degree ≤ compressed.combinationLen := by
  let query : Expression F Query := .var (.fixed ⟨compressed.packedCol⟩ 0)
  let factors := (List.range compressed.combinationLen).filterMap fun j =>
    if j + 1 = compressed.assignedRoot then none
    else some (((j + 1 : ℕ) : F) - query)
  have hlinear : ∀ factor ∈ factors, factor.degree ≤ 1 := by
    intro factor hfactor
    obtain ⟨j, _, hfactor⟩ := List.mem_filterMap.mp hfactor
    split at hfactor
    · simp at hfactor
    · cases Option.some.inj hfactor
      rfl
  have hlength : factors.length < compressed.combinationLen := by
    have hmissing : compressed.assignedRoot - 1 ∈ List.range compressed.combinationLen := by
      rw [List.mem_range]
      omega
    have h : factors.length < (List.range compressed.combinationLen).length :=
      List.length_filterMap_lt_length_iff_exists.mpr
      ⟨compressed.assignedRoot - 1, hmissing, by
        simp only [show compressed.assignedRoot - 1 + 1 = compressed.assignedRoot by omega, ↓reduceIte]⟩
    simpa only [List.length_range] using h
  exact (foldl_mul_degree_le factors query hlinear).trans (by
    change 1 + factors.length ≤ compressed.combinationLen
    omega)

/-- Source expression degree when each selector leaf has the supplied replacement cost. -/
def selectorWeightedDegree {F : Type} (cost : ℕ → ℕ) : Expression F Query → ℕ
  | .var (.selector selector) => cost selector.index
  | .var _ => 1
  | .const _ => 0
  | .add left right => max (selectorWeightedDegree cost left) (selectorWeightedDegree cost right)
  | .mul left right => selectorWeightedDegree cost left + selectorWeightedDegree cost right

/-- Replacing selectors by expressions within their assigned costs respects the weighted source bound. -/
theorem substSelectorMap_degree_le_weighted {F : Type} [Field F]
    (map : ℕ → Option SelCompress) (cost : ℕ → ℕ) (expression : Expression F Query)
    (hcost : ∀ selector ∈ expression.selectorIndices,
      match map selector with
      | none => 1 ≤ cost selector
      | some compressed => (selReplacement (F := F) compressed).degree ≤ cost selector) :
    (substSelectorMap map expression).degree ≤ selectorWeightedDegree cost expression := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          have h := hcost selector.index (by simp [Expression.selectorIndices])
          cases hlookup : map selector.index <;>
            simpa only [substSelectorMap, hlookup, selectorWeightedDegree, Expression.degree] using h
      | fixed | advice | «instance» => exact Nat.le_refl _
  | const => exact Nat.le_refl _
  | add left right ihl ihr =>
      apply max_le_max
      · exact ihl (fun s hs => hcost s (List.mem_append_left _ hs))
      · exact ihr (fun s hs => hcost s (List.mem_append_right _ hs))
  | mul left right ihl ihr =>
      apply Nat.add_le_add
      · exact ihl (fun s hs => hcost s (List.mem_append_left _ hs))
      · exact ihr (fun s hs => hcost s (List.mem_append_right _ hs))

end Zcash.Snark.ZeroKnowledge
