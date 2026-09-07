import Zcash.Circuits.Integration.CopyListMembership
import Clean.Halo2.TopLevel

/-!
# The compiler's copy endpoints stay within its row footprint

The copy stream is the same V1 stream used by permutation key generation, including
the compiler's deferred constant allocation. Existing structural copy-extraction
lemmas supply its row and column bounds for any lawful top-level circuit. No captured
copy list or concrete Action reduction is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The ordered copy tuples consumed by the compiler's permutation assembly. -/
def plonkKeygenCopyRaw (top : TopLevelCircuit Fp Config PublicInput) : List (ℕ × ℕ × ℕ × ℕ) :=
  Layout.V1.copyList (Keygen.permColsOf top.constraintSystem) (FloorPlanner.V1.starts top.operations)
    top.operations (Keygen.constantCopyEntries top.constraintSystem top.operations)

/-- The compiler supplies one deferred constant allocation per constant site. -/
theorem plonkKeygenConstantCopies_fit (top : TopLevelCircuit Fp Config PublicInput) :
    (operationConstSites top.operations).length ≤
      (Keygen.constantCopyEntries top.constraintSystem top.operations).length := by
  rw [Keygen.constantCopyEntries, List.length_map, operationConstSites_length]
  exact top.constantValues_length_le_constantAssignments_length

/-- Every copy endpoint lies below the compiler's operation row footprint. -/
theorem plonkKeygenCopyRaw_rows_lt_usedRows (top : TopLevelCircuit Fp Config PublicInput)
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ plonkKeygenCopyRaw top) :
    tuple.2.1 < Halo2.usedRows top.operations ∧ tuple.2.2.2 < Halo2.usedRows top.operations := by
  apply V1_copyList_rows_lt_usedRows top.operations (Keygen.permColsOf top.constraintSystem)
    (Keygen.constantCopyEntries top.constraintSystem top.operations) (plonkKeygenConstantCopies_fit top)
    _ tuple htuple
  intro entry hentry
  rw [Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact V1_constantAssignments_row_lt_usedRows top.operations
    (top.constraintSystem.constants.map (·.index)) hassignment

/-- Every copy endpoint names one of the compiler's configured permutation columns. -/
theorem plonkKeygenCopyRaw_columns_lt (top : TopLevelCircuit Fp Config PublicInput)
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ plonkKeygenCopyRaw top) :
    tuple.1 < top.permutationColumnCount ∧ tuple.2.2.1 < top.permutationColumnCount := by
  have hcolumns : (Keygen.permColsOf top.constraintSystem).length = top.permutationColumnCount := by
    simp only [Keygen.permColsOf, List.length_map, TopLevelCircuit.permutationColumnCount,
      TopLevelCircuit.permutationColumns]
  rw [← hcolumns]
  apply V1_copyList_columns_lt top.constraintSystem top.operations top.keygenCoherent
    (FloorPlanner.V1.starts top.operations) (Keygen.constantCopyEntries top.constraintSystem top.operations)
    (plonkKeygenConstantCopies_fit top) _ tuple htuple
  intro entry hentry
  rw [Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact top.constantAssignmentColumn_mem_permutationColumns hassignment

end Zcash.Snark.ZeroKnowledge
