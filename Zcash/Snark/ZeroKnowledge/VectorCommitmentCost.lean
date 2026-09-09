import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Commit the complete coefficient vector while retaining both scalar and generator reader costs. -/
def vectorCommitmentCosted (groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (coefficients : Fin n → F × ℕ) : G × ℕ :=
  sumFinCosted groupAdd fun index =>
    let generator := generators index
    let coefficient := coefficients index
    (coefficient.1 • generator.1, coefficient.2 + generator.2 + groupScale + 1)

/-- Erasure is the exact coefficient commitment used by the original IPA. -/
theorem vectorCommitmentCosted_result (groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (coefficients : Fin n → F × ℕ) :
    (vectorCommitmentCosted groupAdd groupScale generators coefficients).1 =
      commitGen (fun index => (generators index).1) (fun index => (coefficients index).1) := by
  simp only [vectorCommitmentCosted, sumFinCosted_result, commitGen]

/-- Complete vector commitment budget from explicit coefficient and generator access bounds. -/
theorem vectorCommitmentCosted_cost_le (groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (coefficients : Fin n → F × ℕ) (generatorRead coefficientRead : ℕ)
    (hg : ∀ index, (generators index).2 ≤ generatorRead)
    (hc : ∀ index, (coefficients index).2 ≤ coefficientRead) :
    (vectorCommitmentCosted groupAdd groupScale generators coefficients).2 ≤
      n * (coefficientRead + generatorRead + groupScale + groupAdd + 2) + n * n + 1 := by
  have h := sumFinCosted_cost_le groupAdd
    (fun index : Fin n => ((coefficients index).1 • (generators index).1,
      (coefficients index).2 + (generators index).2 + groupScale + 1))
    (coefficientRead + generatorRead + groupScale + 1) (by
      intro index
      have ha := hc index
      have hb := hg index
      dsimp only
      omega)
  calc
    _ ≤ n * (coefficientRead + generatorRead + groupScale + 1 + groupAdd + 1) + n * n + 1 := h
    _ = _ := by ring

/-- The scalar inner product is the same counted vector sum with field multiplication. -/
def innerProductCosted (add multiply : ℕ) {n : ℕ}
    (left right : Fin n → F × ℕ) : F × ℕ :=
  vectorCommitmentCosted add multiply right left

/-- Erasure gives the original scalar inner product for every field vector. -/
theorem innerProductCosted_result (add multiply : ℕ) {n : ℕ}
    (left right : Fin n → F × ℕ) :
    (innerProductCosted add multiply left right).1 =
      innerProduct (fun index => (left index).1) (fun index => (right index).1) := by
  simp only [innerProductCosted, vectorCommitmentCosted_result, commitGen, innerProduct, smul_eq_mul]

/-- The complete scalar product counts all reads and arithmetic, including the empty-vector case. -/
theorem innerProductCosted_cost_le (add multiply : ℕ) {n : ℕ}
    (left right : Fin n → F × ℕ) (leftRead rightRead : ℕ)
    (hl : ∀ index, (left index).2 ≤ leftRead) (hr : ∀ index, (right index).2 ≤ rightRead) :
    (innerProductCosted add multiply left right).2 ≤
      n * (leftRead + rightRead + multiply + add + 2) + n * n + 1 :=
  vectorCommitmentCosted_cost_le add multiply right left rightRead leftRead hr hl

end Zcash.Snark.ZeroKnowledge
