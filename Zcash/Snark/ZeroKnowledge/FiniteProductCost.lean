import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge

/-- Counted finite products reuse the same explicit traversal as counted finite sums. -/
def prodFinCosted {α : Type*} [CommMonoid α] (multiply : ℕ) {count : ℕ}
    (read : Fin count → α × ℕ) : α × ℕ :=
  let result := sumFinCosted (α := Additive α) multiply
    (fun index => (Additive.ofMul (read index).1, (read index).2))
  (Additive.toMul result.1, result.2)

/-- Cost erasure is the original finite product. -/
theorem prodFinCosted_result {α : Type*} [CommMonoid α] (multiply : ℕ) {count : ℕ}
    (read : Fin count → α × ℕ) :
    (prodFinCosted multiply read).1 = ∏ index, (read index).1 := by
  simp only [prodFinCosted, sumFinCosted_result, toMul_sum, toMul_ofMul]

/-- The complete product budget includes every factor reader and multiplication. -/
theorem prodFinCosted_cost_le {α : Type*} [CommMonoid α] (multiply : ℕ) {count : ℕ}
    (read : Fin count → α × ℕ) (access : ℕ) (hread : ∀ index, (read index).2 ≤ access) :
    (prodFinCosted multiply read).2 ≤ count * (access + multiply + 1) + count * count + 1 :=
  sumFinCosted_cost_le multiply
    (fun index => (Additive.ofMul (read index).1, (read index).2)) access hread

end Zcash.Snark.ZeroKnowledge
