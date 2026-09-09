import Zcash.Snark.ZeroKnowledge.ActivationCoverageScan

/-!
# Stored data and bounded pieces for complete activation checks

Each metadata list and comparison tree can be normalized once with an equality
certificate. The complete check then composes one kernel-checked predicate per
configured gate or lookup master, without rebuilding a source tree at each row.
-/

namespace Zcash.Snark.ZeroKnowledge
attribute [local instance] lexOrd

/-- The exact Boolean conjunction over an original list. -/
def coverageListAll {α : Type} (predicate : α → Bool) (entries : List α) : Bool := entries.all predicate

/-- A checked head and the complete remaining list establish the original conjunction. -/
theorem coverageListAll_cons {α : Type} (predicate : α → Bool) (entry : α) (rest : List α)
    (hentry : predicate entry = true) (hrest : coverageListAll predicate rest = true) :
    coverageListAll predicate (entry :: rest) = true := by
  simpa only [coverageListAll, List.all_cons, hentry, Bool.true_and] using hrest

/-- Insert a complete list into a comparison tree using an explicit fold. -/
def coverageTreeFold {α : Type} (cmp : α → α → Ordering) (entries : List α)
    (initial : Std.TreeSet α cmp) : Std.TreeSet α cmp :=
  entries.foldl (fun tree entry => tree.insert entry) initial

/-- Each checked list piece is composed with the complete remaining tree construction. -/
theorem coverageTreeFold_chunk {α : Type} (cmp : α → α → Ordering)
    (entries piece rest : List α) (initial next final : Std.TreeSet α cmp)
    (hentries : entries = piece ++ rest) (hstep : coverageTreeFold cmp piece initial = next)
    (hrest : coverageTreeFold cmp rest next = final) :
    coverageTreeFold cmp entries initial = final := by
  rw [hentries]
  dsimp only [coverageTreeFold] at hstep hrest ⊢
  rw [List.foldl_append, hstep]
  exact hrest

/-- The initial named-gate comparison tree. -/
def gateCoverageEmpty : Std.TreeSet (ℕ × String × ℕ) := ∅

/-- The complete comparison tree of original named gate activations. -/
def gateCoverageTree (labels : List (ℕ × String × ℕ)) : Std.TreeSet (ℕ × String × ℕ) :=
  coverageTreeFold compare labels gateCoverageEmpty

/-- Explicit insertion preserves membership in the original complete comparison tree. -/
theorem gateCoverageTree_contains (labels : List (ℕ × String × ℕ)) (value : ℕ × String × ℕ) :
    (gateCoverageTree labels).contains value = (Std.TreeSet.ofList labels compare).contains value :=
  (Std.TreeSet.Equiv.contains_eq Std.TreeSet.ofList_equiv_foldl).symm

/-- One configured gate must retain every activation bearing its selector. -/
def gateCoveragePredicate (activations : List (ℕ × ℕ)) (tree : Std.TreeSet (ℕ × String × ℕ))
    (gate : ℕ × String) : Bool :=
  activations.all fun activation =>
    gate.1 != activation.1 || tree.contains (gate.1, gate.2, activation.2)

/-- The original gate check against an already materialized comparison tree. -/
def gateCoverageAgainst (gates : List (ℕ × String)) (activations : List (ℕ × ℕ))
    (tree : Std.TreeSet (ℕ × String × ℕ)) : Bool :=
  coverageListAll (gateCoveragePredicate activations tree) gates

/-- Exact normalization equalities and the complete stored check imply the original gate scan. -/
theorem gateActivationCoverageScan_stored (gates storedGates : List (ℕ × String))
    (activations storedActivations : List (ℕ × ℕ)) (labels storedLabels : List (ℕ × String × ℕ))
    (tree : Std.TreeSet (ℕ × String × ℕ))
    (hgates : gates = storedGates) (hactivations : activations = storedActivations)
    (hlabels : labels = storedLabels) (htree : gateCoverageTree storedLabels = tree)
    (hcheck : gateCoverageAgainst storedGates storedActivations tree = true) :
    gateActivationCoverageScan gates activations labels = true := by
  rw [hgates, hactivations, hlabels]
  have hscan : gateActivationCoverageScan storedGates storedActivations storedLabels =
      gateCoverageAgainst storedGates storedActivations (gateCoverageTree storedLabels) := by
    unfold gateActivationCoverageScan gateCoverageAgainst coverageListAll
    apply congrArg (fun predicate => storedGates.all predicate)
    funext gate
    simp only [gateCoveragePredicate, gateCoverageTree_contains]
  rw [hscan, htree]
  exact hcheck

/-- The initial lookup-master comparison tree. -/
def lookupCoverageEmpty : Std.TreeSet (ℕ × ℕ) := ∅

/-- The complete comparison tree of original lookup-master activations. -/
def lookupCoverageTree (labels : List (ℕ × ℕ)) : Std.TreeSet (ℕ × ℕ) :=
  coverageTreeFold compare labels lookupCoverageEmpty

/-- Explicit insertion preserves membership in the original complete lookup tree. -/
theorem lookupCoverageTree_contains (labels : List (ℕ × ℕ)) (value : ℕ × ℕ) :
    (lookupCoverageTree labels).contains value = (Std.TreeSet.ofList labels compare).contains value :=
  (Std.TreeSet.Equiv.contains_eq Std.TreeSet.ofList_equiv_foldl).symm

/-- One configured lookup master must retain every original activated row. -/
def lookupCoveragePredicate (activations : List (ℕ × ℕ)) (tree : Std.TreeSet (ℕ × ℕ)) (master : ℕ) : Bool :=
  activations.all fun activation => master != activation.1 || tree.contains (master, activation.2)

/-- The original lookup check against an already materialized comparison tree. -/
def lookupCoverageAgainst (masters : List ℕ) (activations : List (ℕ × ℕ)) (tree : Std.TreeSet (ℕ × ℕ)) : Bool :=
  coverageListAll (lookupCoveragePredicate activations tree) masters

/-- Exact normalization equalities and the complete stored check imply the original lookup scan. -/
theorem lookupActivationCoverageScan_stored (masters storedMasters : List ℕ)
    (activations storedActivations labels storedLabels : List (ℕ × ℕ)) (tree : Std.TreeSet (ℕ × ℕ))
    (hmasters : masters = storedMasters) (hactivations : activations = storedActivations)
    (hlabels : labels = storedLabels) (htree : lookupCoverageTree storedLabels = tree)
    (hcheck : lookupCoverageAgainst storedMasters storedActivations tree = true) :
    lookupActivationCoverageScan masters activations labels = true := by
  rw [hmasters, hactivations, hlabels]
  have hscan : lookupActivationCoverageScan storedMasters storedActivations storedLabels =
      lookupCoverageAgainst storedMasters storedActivations (lookupCoverageTree storedLabels) := by
    unfold lookupActivationCoverageScan lookupCoverageAgainst coverageListAll
    apply congrArg (fun predicate => storedMasters.all predicate)
    funext master
    simp only [lookupCoveragePredicate, lookupCoverageTree_contains]
  rw [hscan, htree]
  exact hcheck

end Zcash.Snark.ZeroKnowledge
