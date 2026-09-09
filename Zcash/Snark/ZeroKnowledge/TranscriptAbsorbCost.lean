import Zcash.Snark.ZeroKnowledge.ListCollectedCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.PermutationBoundaryCost
import Zcash.Snark.ZeroKnowledge.LookupExpressionsCost
import Zcash.Snark.Verifier.FiatShamir

/-!
# Counted construction of typed transcript blocks

Every field supplies its complete producer cost. Finite collection forces all
fields and charges the original order's index adapters and output cells. The
append operation retains both input producers and every copied prefix cell.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Append two produced lists without dropping either producer's cost. -/
def appendProducedCosted {α : Type*} (left right : List α × ℕ) : List α × ℕ :=
  let joined := appendListCosted left.1 right.1
  (joined.1, left.2 + right.2 + joined.2 + 1)

/-- Produced-list append preserves the exact element order. -/
theorem appendProducedCosted_result {α : Type*} (left right : List α × ℕ) :
    (appendProducedCosted left right).1 = left.1 ++ right.1 :=
  appendListCosted_result _ _

/-- Both producers and the copied prefix remain in the exact append cost. -/
theorem appendProducedCosted_cost {α : Type*} (left right : List α × ℕ) :
    (appendProducedCosted left right).2 = left.2 + right.2 + left.1.length + 2 := by
  simp only [appendProducedCosted, appendListCosted_cost]
  omega

/-- Materialize a point vector with every complete point-reader cost. -/
def absorbPointsCosted {F G : Type*} {count : ℕ}
    (points : Fin count → G × ℕ) : List (TranscriptElt F G) × ℕ :=
  ofFnCosted (fun index => (.point (points index).1, (points index).2 + 1))

/-- Point materialization agrees with the verifier's original absorption. -/
theorem absorbPointsCosted_result {F G : Type*} {count : ℕ}
    (points : Fin count → G × ℕ) :
    (absorbPointsCosted (F := F) points).1 = absorbPoints (fun index => (points index).1) :=
  ofFnCosted_result _

/-- The complete point block has one item per supplied point. -/
theorem absorbPointsCosted_length {F G : Type*} {count : ℕ}
    (points : Fin count → G × ℕ) :
    (absorbPointsCosted (F := F) points).1.length = count := ofFnCosted_length _

/-- Point-block cost includes all input computations, tags, and finite collection. -/
theorem absorbPointsCosted_cost_le {F G : Type*} {count : ℕ}
    (points : Fin count → G × ℕ) (access : ℕ)
    (hread : ∀ index, (points index).2 ≤ access) :
    (absorbPointsCosted (F := F) points).2 ≤ count * (access + 2) + count * count + 1 := by
  exact ofFnCosted_cost_le _ _ (fun index => Nat.add_le_add_right (hread index) 1)

/-- Materialize a scalar vector with every complete scalar-reader cost. -/
def absorbScalarsCosted {F G : Type*} {count : ℕ}
    (scalars : Fin count → F × ℕ) : List (TranscriptElt F G) × ℕ :=
  ofFnCosted (fun index => (.scalar (scalars index).1, (scalars index).2 + 1))

/-- Scalar materialization agrees with the verifier's original absorption. -/
theorem absorbScalarsCosted_result {F G : Type*} {count : ℕ}
    (scalars : Fin count → F × ℕ) :
    (absorbScalarsCosted (G := G) scalars).1 = absorbScalars (fun index => (scalars index).1) :=
  ofFnCosted_result _

/-- The complete scalar block has one item per supplied scalar. -/
theorem absorbScalarsCosted_length {F G : Type*} {count : ℕ}
    (scalars : Fin count → F × ℕ) :
    (absorbScalarsCosted (G := G) scalars).1.length = count := ofFnCosted_length _

/-- Scalar-block cost includes every producer and finite collection step. -/
theorem absorbScalarsCosted_cost_le {F G : Type*} {count : ℕ}
    (scalars : Fin count → F × ℕ) (access : ℕ)
    (hread : ∀ index, (scalars index).2 ≤ access) :
    (absorbScalarsCosted (G := G) scalars).2 ≤ count * (access + 2) + count * count + 1 := by
  exact ofFnCosted_cost_le _ _ (fun index => Nat.add_le_add_right (hread index) 1)

/-- Materialize a proof-major matrix of point blocks. -/
def absorbPoints2Costed {F G : Type*} {rows columns : ℕ}
    (points : Fin rows → Fin columns → G × ℕ) : List (TranscriptElt F G) × ℕ :=
  flattenFinCosted (fun row => absorbPointsCosted (F := F) (points row))

/-- The counted matrix has exactly the verifier's proof-major order. -/
theorem absorbPoints2Costed_result {F G : Type*} {rows columns : ℕ}
    (points : Fin rows → Fin columns → G × ℕ) :
    (absorbPoints2Costed (F := F) points).1 = absorbPoints2 (fun row column => (points row column).1) := by
  simp only [absorbPoints2Costed, flattenFinCosted_result, absorbPointsCosted_result, absorbPoints2]

/-- Every matrix point contributes one transcript item. -/
theorem absorbPoints2Costed_length {F G : Type*} {rows columns : ℕ}
    (points : Fin rows → Fin columns → G × ℕ) :
    (absorbPoints2Costed (F := F) points).1.length = rows * columns := by
  simp [absorbPoints2Costed, flattenFinCosted_result, List.length_flatten, Function.comp_def,
    absorbPointsCosted_length]

/-- The matrix bound retains inner and outer finite collection. -/
theorem absorbPoints2Costed_cost_le {F G : Type*} {rows columns : ℕ}
    (points : Fin rows → Fin columns → G × ℕ) (access : ℕ)
    (hread : ∀ row column, (points row column).2 ≤ access) :
    (absorbPoints2Costed (F := F) points).2 ≤
      rows * (columns * (access + 2) + columns * columns + columns + 3) + rows * rows + 1 := by
  have h := flattenFinCosted_cost_le (fun row => absorbPointsCosted (F := F) (points row))
    (columns * (access + 2) + columns * columns + 1) columns
    (fun row => absorbPointsCosted_cost_le (points row) access (hread row))
    (fun row => le_of_eq (absorbPointsCosted_length (points row)))
  dsimp only [absorbPoints2Costed]
  convert h using 1
  ring

/-- Materialize a proof-major matrix of scalar blocks. -/
def absorbScalars2Costed {F G : Type*} {rows columns : ℕ}
    (scalars : Fin rows → Fin columns → F × ℕ) : List (TranscriptElt F G) × ℕ :=
  flattenFinCosted (fun row => absorbScalarsCosted (G := G) (scalars row))

/-- The scalar matrix retains the verifier's original row and column order. -/
theorem absorbScalars2Costed_result {F G : Type*} {rows columns : ℕ}
    (scalars : Fin rows → Fin columns → F × ℕ) :
    (absorbScalars2Costed (G := G) scalars).1 = absorbScalars2 (fun row column => (scalars row column).1) := by
  simp only [absorbScalars2Costed, flattenFinCosted_result, absorbScalarsCosted_result, absorbScalars2]

/-- Every matrix scalar contributes one transcript item. -/
theorem absorbScalars2Costed_length {F G : Type*} {rows columns : ℕ}
    (scalars : Fin rows → Fin columns → F × ℕ) :
    (absorbScalars2Costed (G := G) scalars).1.length = rows * columns := by
  simp [absorbScalars2Costed, flattenFinCosted_result, List.length_flatten, Function.comp_def,
    absorbScalarsCosted_length]

/-- The scalar matrix bound pays for all inner and outer collection work. -/
theorem absorbScalars2Costed_cost_le {F G : Type*} {rows columns : ℕ}
    (scalars : Fin rows → Fin columns → F × ℕ) (access : ℕ)
    (hread : ∀ row column, (scalars row column).2 ≤ access) :
    (absorbScalars2Costed (G := G) scalars).2 ≤
      rows * (columns * (access + 2) + columns * columns + columns + 3) + rows * rows + 1 := by
  have h := flattenFinCosted_cost_le (fun row => absorbScalarsCosted (G := G) (scalars row))
    (columns * (access + 2) + columns * columns + 1) columns
    (fun row => absorbScalarsCosted_cost_le (scalars row) access (hread row))
    (fun row => le_of_eq (absorbScalarsCosted_length (scalars row)))
  dsimp only [absorbScalars2Costed]
  convert h using 1
  ring

end Zcash.Snark.ZeroKnowledge
