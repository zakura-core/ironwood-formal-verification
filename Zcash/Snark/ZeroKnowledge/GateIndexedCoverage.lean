import Zcash.Snark.ZeroKnowledge.ActivationCoverageData

/-!
# Exact gate coverage using finite configured-name indices

An index names the complete configured selector/name pair. Unknown source labels
receive the out-of-range index, which cannot equal any configured gate's index.
The resulting numeric comparison tree preserves every original Boolean result,
including missing names, wrong rows, and gates sharing a selector.
-/

namespace Zcash.Snark.ZeroKnowledge
attribute [local instance] lexOrd

/-- Encode the complete gate identity and retain its original placed row. -/
def gateCoverageIndexLabel (gates : List (ℕ × String)) (label : ℕ × String × ℕ) : ℕ × ℕ :=
  (gates.idxOf (label.1, label.2.1), label.2.2)

/-- A configured gate index cannot be confused with any different source label. -/
theorem gateCoverageIndexLabel_eq_iff (gates : List (ℕ × String)) (gate : ℕ × String)
    (hgate : gate ∈ gates) (row : ℕ) (label : ℕ × String × ℕ) :
    gateCoverageIndexLabel gates label = (gates.idxOf gate, row) ↔
      label = (gate.1, gate.2, row) := by
  constructor
  · intro h
    have hid : gate = (label.1, label.2.1) :=
      (List.idxOf_inj hgate).mp (congrArg Prod.fst h).symm
    have hrow : label.2.2 = row := congrArg Prod.snd h
    have hselector : label.1 = gate.1 := congrArg (fun entry : ℕ × String => entry.1) hid.symm
    have hname : label.2.1 = gate.2 := congrArg (fun entry : ℕ × String => entry.2) hid.symm
    exact Prod.ext hselector (Prod.ext hname hrow)
  · rintro rfl
    rfl

/-- Membership after indexing retains the exact source name and row of every configured gate. -/
theorem gateCoverageIndexLabel_mem_iff (gates : List (ℕ × String)) (gate : ℕ × String)
    (hgate : gate ∈ gates) (row : ℕ) (labels : List (ℕ × String × ℕ)) :
    (gates.idxOf gate, row) ∈ labels.map (gateCoverageIndexLabel gates) ↔
      (gate.1, gate.2, row) ∈ labels := by
  constructor
  · intro h
    obtain ⟨label, hlabel, heq⟩ := List.mem_map.mp h
    rw [(gateCoverageIndexLabel_eq_iff gates gate hgate row label).mp heq] at hlabel
    exact hlabel
  · intro h
    exact List.mem_map.mpr ⟨(gate.1, gate.2, row), h, rfl⟩

/-- Check a selector/index pair against the numeric source tree. -/
def gateIndexedCoveragePredicate (activations : List (ℕ × ℕ)) (tree : Std.TreeSet (ℕ × ℕ))
    (gate : ℕ × ℕ) : Bool :=
  activations.all fun activation =>
    gate.1 != activation.1 || tree.contains (gate.2, activation.2)

/-- The complete scan on materialized selector/index pairs and indexed source rows. -/
def gateIndexedCoverageScan (gates activations labels : List (ℕ × ℕ)) : Bool :=
  coverageListAll (gateIndexedCoveragePredicate activations (Std.TreeSet.ofList labels compare)) gates

/-- Reindexing the original finite gate registry preserves the entire original coverage result. -/
theorem gateIndexedCoverageScan_original (gates : List (ℕ × String))
    (activations : List (ℕ × ℕ)) (labels : List (ℕ × String × ℕ)) :
    gateIndexedCoverageScan (gates.map (fun gate => (gate.1, gates.idxOf gate))) activations
      (labels.map (gateCoverageIndexLabel gates)) = gateActivationCoverageScan gates activations labels := by
  have hcontains (gate : ℕ × String) (hgate : gate ∈ gates) (row : ℕ) :
      (Std.TreeSet.ofList (labels.map (gateCoverageIndexLabel gates)) compare).contains (gates.idxOf gate, row) =
      (Std.TreeSet.ofList labels compare).contains (gate.1, gate.2, row) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [Std.TreeSet.contains_ofList, List.contains_iff_mem] using
      gateCoverageIndexLabel_mem_iff gates gate hgate row labels
  apply Bool.eq_iff_iff.mpr
  simp only [gateIndexedCoverageScan, coverageListAll, List.all_map, Function.comp_def,
    gateIndexedCoveragePredicate, gateActivationCoverageScan, List.all_eq_true]
  constructor <;> intro h gate hgate activation hactivation
  · simpa only [hcontains gate hgate activation.2] using h gate hgate activation hactivation
  · simpa only [hcontains gate hgate activation.2] using h gate hgate activation hactivation

/-- Exact stored-data equalities and the complete numeric check imply the original indexed scan. -/
theorem gateIndexedCoverageScan_stored (gates storedGates activations storedActivations labels storedLabels : List (ℕ × ℕ))
    (tree : Std.TreeSet (ℕ × ℕ)) (hgates : gates = storedGates) (hactivations : activations = storedActivations)
    (hlabels : labels = storedLabels) (htree : lookupCoverageTree storedLabels = tree)
    (hcheck : coverageListAll (gateIndexedCoveragePredicate storedActivations tree) storedGates = true) :
    gateIndexedCoverageScan gates activations labels = true := by
  rw [hgates, hactivations, hlabels]
  have hscan : gateIndexedCoverageScan storedGates storedActivations storedLabels =
      coverageListAll (gateIndexedCoveragePredicate storedActivations (lookupCoverageTree storedLabels)) storedGates := by
    unfold gateIndexedCoverageScan coverageListAll
    apply congrArg (fun predicate => storedGates.all predicate)
    funext gate
    simp only [gateIndexedCoveragePredicate, lookupCoverageTree_contains]
  rw [hscan, htree]
  exact hcheck

end Zcash.Snark.ZeroKnowledge
