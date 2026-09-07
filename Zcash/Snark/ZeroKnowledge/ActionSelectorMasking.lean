import Zcash.Snark.ZeroKnowledge.ActionSourceMasking
import Zcash.Snark.ZeroKnowledge.ActionQueryMasking
import Zcash.Circuits.Integration.SelectorCoherence

/-!
# Selector substitution in the Action masking certificates

The compressor places every allocated selector in the new fixed-column suffix.
For the initial boundary, nine source selectors must route to the four declared
zero columns. This routing is an explicit packing condition. Under that condition,
the proved source certificates survive the actual compiler's selector replacement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- The initial-row source selectors must route to the four public columns declared zero there. -/
def ActionPreviousSelectorPacking : Prop :=
  ∀ selector ∈ actionPreviousRowSelectors, ∀ compressed,
    actionCircuit.selectorMap.lookup selector = some compressed →
      compressed.packedCol ∈ plonkInitialMaskColumns

/-- The public fixed queries used as zeros after actual selector substitution. -/
def actionPackedMaskZero (initial : Bool) : Query → Bool
  | .fixed column rotation => (rotation = 0 && 14 ≤ column.index && column.index < 29) &&
      (!initial || column.index ∈ plonkInitialMaskColumns)
  | _ => false

/-- Every emitted Action selector replacement uses a column in the packed suffix. -/
theorem actionCircuit_packedSelectorBounds
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) (selector : ℕ) (compressed : SelCompress)
    (hlookup : actionCircuit.selectorMap.lookup selector = some compressed) :
    14 ≤ compressed.packedCol ∧ compressed.packedCol < 29 := by
  rw [actionCircuit.selectorMap_eq_derive] at hlookup
  obtain ⟨index, hindex, hcolumn⟩ := deriveSelCompressMap_lookup_packedColumn
    actionCircuit.constraintSystem actionCircuit.n actionCircuit.selectorActivations hlookup
  rw [← actionCircuit.selectorMap_eq_derive, hpacked] at hindex
  rw [actionCircuit_numFixedColumns_eq] at hcolumn
  omega

/-- Source zero and safety certificates survive the actual Action selector substitution. -/
theorem actionCircuit_substitutedSourceMaskCertificates
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) (initial : Bool) (expression : Expression Fp Query) :
    (sourceExpressionZero (actionSourceMaskZero initial) expression = true →
      sourceExpressionZero (actionPackedMaskZero initial)
        (substSelectorMap actionCircuit.selectorMap.lookup expression) = true) ∧
    (sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial) expression = true →
      sourceExpressionMaskSafe (actionPackedMaskZero initial) (actionSourceMaskSafe initial)
        (substSelectorMap actionCircuit.selectorMap.lookup expression) = true) := by
  apply substSelectorMap_sourceMaskCertificates
  · intro query hquery
    cases query with
    | fixed | advice | «instance» => simp [actionSourceMaskZero] at hquery
    | selector selector =>
        change (decide (selector.index < 56) &&
          (!initial || decide (selector.index ∈ actionPreviousRowSelectors))) = true at hquery
        simp only [Bool.and_eq_true] at hquery
        obtain ⟨hbound, hzero⟩ := hquery
        have hcovered : (actionCircuit.selectorMap.lookup selector.index).isSome = true := by
          rw [actionCircuit.selectorMap_eq_derive]
          apply deriveSelCompressMap_lookup_isSome_of_lt
          have hcount : actionCircuit.constraintSystem.numSelectors = 56 := actionCircuit_selectorCount_eq
          rw [hcount]
          exact of_decide_eq_true hbound
        cases hlookup : actionCircuit.selectorMap.lookup selector.index with
        | none => simp [hlookup] at hcovered
        | some compressed =>
            simp only [substSelectorMap, hlookup]
            apply selReplacement_sourceExpressionZero
            have hcolumn := actionCircuit_packedSelectorBounds hpacked selector.index compressed hlookup
            cases initial with
            | false => simp [actionPackedMaskZero, hcolumn.1, hcolumn.2]
            | true =>
                have hmember : selector.index ∈ actionPreviousRowSelectors := by simpa using hzero
                simp [actionPackedMaskZero, hcolumn.1, hcolumn.2, hprevious _ hmember _ hlookup]
  · intro query hquery
    cases query with
    | fixed | advice | «instance» => exact hquery
    | selector selector =>
        simp only [substSelectorMap]
        cases hlookup : actionCircuit.selectorMap.lookup selector.index with
        | none => rfl
        | some compressed =>
            exact selReplacement_sourceExpressionMaskSafe _ _ compressed rfl

end Zcash.Snark.ZeroKnowledge
