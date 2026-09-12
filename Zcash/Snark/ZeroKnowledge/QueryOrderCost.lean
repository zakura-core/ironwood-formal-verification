import Zcash.Snark.ZeroKnowledge.ListRoutingCost
import Zcash.Snark.ZeroKnowledge.PlonkOpening

/-!
# Counted fixed and advice query-order routing

Materialized copies of the two fixed query tables are proved to agree with the
original finite functions. Costs include their construction and the entire
list search; no arbitrary source function is assigned a constant access price.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Build and read the original 29-entry fixed-query order. -/
def fixedQueryOrderCosted (index : Fin 29) : Fin 29 × ℕ :=
  let table : List (Fin 29) := [3, 0, 11, 4, 5, 6, 7, 8, 9, 10, 12, 1, 2, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
  let result := getDListCosted 1 0 table index.val
  (result.1, result.2 + 59)

/-- Every computed fixed-query index agrees with the verifier's original table. -/
theorem fixedQueryOrderCosted_result (index : Fin 29) :
    (fixedQueryOrderCosted index).1 = plonkFixedQueryOrder index := by
  fin_cases index <;> rfl

/-- The fixed-table bound includes all literals, list cells, and routing steps. -/
theorem fixedQueryOrderCosted_cost_le (index : Fin 29) :
    (fixedQueryOrderCosted index).2 ≤ 119 := by
  have h := getDListCosted_cost_le 1 (0 : Fin 29)
    [3, 0, 11, 4, 5, 6, 7, 8, 9, 10, 12, 1, 2, 13, 14, 15, 16, 17, 18, 19, 20, 21,
      22, 23, 24, 25, 26, 27, 28] index.val
  change _ + 59 ≤ 119
  norm_num only [List.length_cons, List.length_nil] at h
  omega

/-- Build and read the original 25-entry advice-column and rotation table. -/
def adviceQueryOrderCosted (index : Fin 25) : (Fin 10 × Fin 3) × ℕ :=
  let table : List (Fin 10 × Fin 3) :=
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
      (9, 1), (9, 2), (2, 1), (3, 1), (4, 1), (5, 1), (0, 1), (1, 1), (7, 1), (8, 1),
      (6, 2), (1, 2), (6, 1), (7, 2), (8, 2)]
  let result := getDListCosted 1 (0, 0) table index.val
  (result.1, result.2 + 101)

/-- Both coordinates of every advice query agree with the verifier's original table. -/
theorem adviceQueryOrderCosted_result (index : Fin 25) :
    (adviceQueryOrderCosted index).1 = plonkAdviceQueryOrder index := by
  fin_cases index <;> rfl

/-- Advice-query routing includes both finite indices, pair construction, and list traversal. -/
theorem adviceQueryOrderCosted_cost_le (index : Fin 25) :
    (adviceQueryOrderCosted index).2 ≤ 153 := by
  have h := getDListCosted_cost_le 1 ((0, 0) : Fin 10 × Fin 3)
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
      (9, 1), (9, 2), (2, 1), (3, 1), (4, 1), (5, 1), (0, 1), (1, 1), (7, 1), (8, 1),
      (6, 2), (1, 2), (6, 1), (7, 2), (8, 2)] index.val
  change _ + 101 ≤ 153
  norm_num only [List.length_cons, List.length_nil] at h
  omega

end Zcash.Snark.ZeroKnowledge
