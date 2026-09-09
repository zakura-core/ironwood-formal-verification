import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The original totalized default for a missing stored opening. -/
def emptyStoredOpeningGroup : StoredOpeningGroup := ⟨[], [], 0⟩

/-- Read the first complete opening record before selecting its stored coefficients. -/
def storedFirstOpeningCosted (read : ℕ) (groups : List StoredOpeningGroup) : List Fp × ℕ :=
  let group := getDListCosted read emptyStoredOpeningGroup groups 0
  (group.1.coefficients, group.2 + 1)

/-- First-group reads preserve the same original polynomial and missing-record default. -/
theorem storedFirstOpeningCosted_result (read : ℕ) (groups : List StoredOpeningGroup) :
    densePolynomial (storedFirstOpeningCosted read groups).1 =
      ((groups.map StoredOpeningGroup.erase).getD 0 emptyStoredOpeningGroup.erase).polynomial := by
  rewrite [List.getD_map groups emptyStoredOpeningGroup StoredOpeningGroup.erase]
  simp only [storedFirstOpeningCosted, getDListCosted_result, StoredOpeningGroup.erase]

/-- The first stored group retains the common coefficient capacity, including an empty list. -/
theorem storedFirstOpeningCosted_width (read width : ℕ) (groups : List StoredOpeningGroup)
    (hw : ∀ group ∈ groups, group.coefficients.length ≤ width) :
    (storedFirstOpeningCosted read groups).1.length ≤ width :=
  getDListCosted_property read emptyStoredOpeningGroup groups
    (fun group => group.coefficients.length ≤ width) (Nat.zero_le _) hw 0

/-- The record traversal and subsequent coefficient-field selection are both counted. -/
theorem storedFirstOpeningCosted_cost_le (read : ℕ) (groups : List StoredOpeningGroup) :
    (storedFirstOpeningCosted read groups).2 ≤ 2 * groups.length + read + 2 := by
  have h := getDListCosted_cost_le read emptyStoredOpeningGroup groups 0
  change (getDListCosted read emptyStoredOpeningGroup groups 0).2 + 1 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
