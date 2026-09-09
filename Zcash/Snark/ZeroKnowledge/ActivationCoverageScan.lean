import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Std.Data.TreeSet.Lemmas
import Init.Data.Ord.String

/-!
# Kernel-reducible activation coverage

The original hash-set check has the desired semantics, but its string and pair
hashes are opaque runtime primitives. Comparison trees support kernel reduction.
The equalities below prove that this change preserves the complete original
Boolean result for all lists, including missing names, rows, and lookup masters.
-/

namespace Zcash.Snark.ZeroKnowledge

attribute [local instance] lexOrd

/-- Check every original gate name and row using a reducible comparison tree. -/
def gateActivationCoverageScan (gates : List (ℕ × String))
    (activations : List (ℕ × ℕ)) (labels : List (ℕ × String × ℕ)) : Bool :=
  let emitted := Std.TreeSet.ofList labels compare
  gates.all fun gate => activations.all fun activation =>
    gate.1 != activation.1 || emitted.contains (gate.1, gate.2, activation.2)

/-- The tree scan retains exactly every success and rejection of the original gate check. -/
theorem gateActivationCoverageScan_eq (gates : List (ℕ × String))
    (activations : List (ℕ × ℕ)) (labels : List (ℕ × String × ℕ)) :
    gateActivationCoverageScan gates activations labels = gateActivationCoverageCheck gates activations labels := by
  simp only [gateActivationCoverageScan, gateActivationCoverageCheck,
    Std.TreeSet.contains_ofList, Std.HashSet.contains_ofList]

/-- Check every original lookup master and row using a reducible comparison tree. -/
def lookupActivationCoverageScan (masters : List ℕ)
    (activations labels : List (ℕ × ℕ)) : Bool :=
  let emitted := Std.TreeSet.ofList labels compare
  masters.all fun master => activations.all fun activation =>
    master != activation.1 || emitted.contains (master, activation.2)

/-- The tree scan retains exactly every success and rejection of the original lookup check. -/
theorem lookupActivationCoverageScan_eq (masters : List ℕ) (activations labels : List (ℕ × ℕ)) :
    lookupActivationCoverageScan masters activations labels = lookupActivationCoverageCheck masters activations labels := by
  simp only [lookupActivationCoverageScan, lookupActivationCoverageCheck,
    Std.TreeSet.contains_ofList, Std.HashSet.contains_ofList]

end Zcash.Snark.ZeroKnowledge
