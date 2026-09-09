import Zcash.Snark.ZeroKnowledge.FiniteListReadCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost

namespace Zcash.Snark.ZeroKnowledge

/-- Construct and traverse the original private-column order at a valid commitment index. -/
def privateColumnAtCosted (read : ℕ) {actions : ℕ} (index : Fin (22 * actions)) : PrivateColumnId actions × ℕ :=
  let order := privateColumnOrderCosted actions
  let result := getFinListCosted read order.1
    ⟨index.val, by rewrite [privateColumnOrderCosted_length]; exact index.isLt⟩
  (result.1, order.2 + result.2 + 2)

/-- Erasure reads exactly the original scheduled column identity. -/
theorem privateColumnAtCosted_result (read : ℕ) {actions : ℕ} (index : Fin (22 * actions)) :
    (privateColumnAtCosted read index).1 = privateColumnAt index := by
  simp only [privateColumnAtCosted, getFinListCosted_result, privateColumnOrderCosted_result, privateColumnAt]

/-- The identity read includes original schedule construction and full bounded-index traversal. -/
theorem privateColumnAtCosted_cost_le (read : ℕ) {actions : ℕ} (index : Fin (22 * actions)) :
    (privateColumnAtCosted read index).2 ≤ 4 * actions * actions + 304 * actions + read + 14 := by
  have ho := privateColumnOrderCosted_cost_le actions
  have hr := getFinListCosted_cost_le read (privateColumnOrderCosted actions).1
    ⟨index.val, by rewrite [privateColumnOrderCosted_length]; exact index.isLt⟩
  have hlength := privateColumnOrderCosted_length actions
  change (privateColumnOrderCosted actions).2 +
    (getFinListCosted read (privateColumnOrderCosted actions).1
      ⟨index.val, by rewrite [privateColumnOrderCosted_length]; exact index.isLt⟩).2 + 2 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
