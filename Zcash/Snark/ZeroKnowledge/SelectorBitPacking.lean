import Zcash.Snark.ZeroKnowledge.SelectorActivationBits
import Zcash.Snark.ZeroKnowledge.SelectorCompressionCount

/-!
# The selector packing count through activation bit vectors

The compact calculation carries selector indices and bitwise conflict tests
through the compiler's greedy combination loop. The refinement below checks
every degree-budget, conflict, and fuel branch against the original loop. It
preserves the final count without constructing decoded activation rows during
the finite calculation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

private def extendIndices (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool) (budget : ℕ) :
    ℕ → List ℕ → List ℕ → List ℕ × List ℕ
  | _, combination, [] => (combination, [])
  | currentDegree, combination, selector :: rest =>
      if currentDegree + combination.length = budget then
        (combination, selector :: rest)
      else if combination.any (fun other => conflicts other selector) then
        let (combined, remaining) := extendIndices degree conflicts budget currentDegree combination rest
        (combined, selector :: remaining)
      else
        let nextDegree := max currentDegree (degree selector - 1)
        if nextDegree + combination.length + 1 > budget then
          let (combined, remaining) := extendIndices degree conflicts budget currentDegree combination rest
          (combined, selector :: remaining)
        else
          extendIndices degree conflicts budget nextDegree (combination ++ [selector]) rest

private def combineIndices (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool) (budget : ℕ) :
    ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, selector :: rest =>
      let (combination, remaining) := extendIndices degree conflicts budget (degree selector - 1) [selector] rest
      combination :: combineIndices degree conflicts budget fuel remaining

private def indexPackingCount (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool)
    (budget : ℕ) (selectors : List ℕ) : ℕ :=
  let zeroDegree := selectors.filter (fun selector => degree selector = 0)
  let remaining := selectors.filter (fun selector => degree selector ≠ 0)
  zeroDegree.length + (combineIndices degree conflicts budget remaining.length remaining).length

private theorem extendIndices_eq (describe : ℕ → SelectorDescription)
    (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool) (budget : ℕ)
    (hdegree : ∀ selector, (describe selector).maxDegree = degree selector)
    (hconflicts : ∀ left right, (describe left).conflicts (describe right) = conflicts left right)
    (currentDegree : ℕ) (combination rest : List ℕ) :
    extendCombination budget currentDegree (combination.map describe) (rest.map describe) =
      Prod.map (List.map describe) (List.map describe)
        (extendIndices degree conflicts budget currentDegree combination rest) := by
  induction rest generalizing currentDegree combination with
  | nil => rfl
  | cons selector rest ih =>
      by_cases hfull : currentDegree + combination.length = budget
      · simp [extendCombination, extendIndices, hfull]
      · by_cases hconflict : combination.any (fun other => conflicts other selector) = true
        · simp only [List.map_cons, extendCombination, extendIndices, List.length_map,
            List.any_map, Function.comp_def, hconflicts, hfull, if_false, hconflict, if_true]
          rw [ih]
          cases extendIndices degree conflicts budget currentDegree combination rest
          rfl
        · by_cases hbudget : max currentDegree (degree selector - 1) + combination.length + 1 > budget
          · simp only [List.map_cons, extendCombination, extendIndices, List.length_map,
              List.any_map, Function.comp_def, hconflicts, hdegree, hfull, if_false,
              hconflict, Bool.false_eq_true, hbudget, if_true]
            rw [ih]
            cases extendIndices degree conflicts budget currentDegree combination rest
            rfl
          · simpa only [List.map_cons, extendCombination, extendIndices, List.length_map,
              List.any_map, Function.comp_def, hconflicts, hdegree, hfull, if_false,
              hconflict, Bool.false_eq_true, hbudget, List.map_append, List.map_singleton,
              List.map_nil] using
              ih (max currentDegree (degree selector - 1)) (combination ++ [selector])

private theorem combineIndices_eq (describe : ℕ → SelectorDescription)
    (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool) (budget : ℕ)
    (hdegree : ∀ selector, (describe selector).maxDegree = degree selector)
    (hconflicts : ∀ left right, (describe left).conflicts (describe right) = conflicts left right)
    (fuel : ℕ) (selectors : List ℕ) :
    buildCombinations budget fuel (selectors.map describe) =
      (combineIndices degree conflicts budget fuel selectors).map (List.map describe) := by
  induction fuel generalizing selectors with
  | zero => rfl
  | succ fuel ih =>
      cases selectors with
      | nil => rfl
      | cons selector rest =>
          simp only [List.map_cons, buildCombinations, combineIndices, hdegree]
          rw [show [describe selector] = [selector].map describe by rfl,
            extendIndices_eq describe degree conflicts budget hdegree hconflicts]
          cases extendIndices degree conflicts budget (degree selector - 1) [selector] rest
          simp only [Prod.map]
          rw [ih]

private theorem process_map_count (describe : ℕ → SelectorDescription)
    (degree : ℕ → ℕ) (conflicts : ℕ → ℕ → Bool) (budget : ℕ)
    (hdegree : ∀ selector, (describe selector).maxDegree = degree selector)
    (hconflicts : ∀ left right, (describe left).conflicts (describe right) = conflicts left right)
    (selectors : List ℕ) :
    (process (selectors.map describe) budget).newFixedCols =
      indexPackingCount degree conflicts budget selectors := by
  simp only [process, indexPackingCount, List.filter_map, Function.comp_def, hdegree, List.length_map]
  rw [combineIndices_eq describe degree conflicts budget hdegree hconflicts]
  simp

/-- Evaluate the equivalent index-based packer with bitwise conflict tests. -/
irreducible_def selectorBitPackingCount (rows selectors budget : ℕ)
    (degrees : Array ℕ) (activations : List (ℕ × ℕ)) : ℕ :=
  let table := selectorActivationBits rows selectors activations
  indexPackingCount (fun index => degrees[index]!)
    (fun left right => decide (table[left]! &&& table[right]! ≠ 0)) budget (List.range selectors)

/-- The compact calculation returns exactly the original compiler packing count. -/
theorem selectorPackingCount_eq_bits (rows selectors budget : ℕ)
    (degrees : Array ℕ) (activations : List (ℕ × ℕ)) :
    selectorPackingCount rows selectors budget degrees activations =
      selectorBitPackingCount rows selectors budget degrees activations := by
  rw [selectorPackingCount, selectorBitPackingCount, activationTable_eq_selectorBitsRows]
  let table := selectorActivationBits rows selectors activations
  let describe := fun index => SelectorDescription.mk index (selectorBitsRows table[index]!) degrees[index]!
  calc
    _ = (process ((List.range selectors).map describe) budget).newFixedCols := by
      apply congrArg (fun descriptions => (process descriptions budget).newFixedCols)
      apply List.map_congr_left
      intro index hindex
      have hbound : index < table.size := by
        rw [selectorActivationBits_size]
        exact List.mem_range.mp hindex
      have hread : (table.map selectorBitsRows)[index]! = selectorBitsRows table[index]! := by
        rw [getElem!_pos (table.map selectorBitsRows) index (by simpa using hbound),
          Array.getElem_map, getElem!_pos table index hbound]
      change SelectorDescription.mk index (table.map selectorBitsRows)[index]! degrees[index]! = describe index
      rw [hread]
    _ = _ := process_map_count describe _ _ budget (fun _ => rfl)
      (fun left right => selectorBitsRows_conflicts table[left]! table[right]! left right _ _) _

end Zcash.Snark.ZeroKnowledge
