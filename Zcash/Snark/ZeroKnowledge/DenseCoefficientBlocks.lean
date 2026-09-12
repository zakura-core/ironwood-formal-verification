import Zcash.Snark.ZeroKnowledge.DenseRowPolynomial
import Zcash.Snark.ZeroKnowledge.QuotientPieces
import Zcash.Snark.ZeroKnowledge.ListRoutingCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Materialize a coefficient block, charging every index calculation and stored read. -/
def denseCoefficientBlockCosted (read size block : ℕ) (values : List Fp) : List Fp × ℕ :=
  ofFnCosted fun index : Fin size =>
    let value := getDListCosted read 0 values (size * block + index.val)
    (value.1, value.2 + 2)

/-- Every stored block represents the original coefficient-block operation. -/
theorem denseCoefficientBlockCosted_result (read size block : ℕ) (values : List Fp) :
    densePolynomial (denseCoefficientBlockCosted read size block values).1 =
      polynomialCoefficientBlock size block (densePolynomial values) := by
  simp only [denseCoefficientBlockCosted, ofFnCosted_result, getDListCosted_result,
    densePolynomial_ofFn, polynomialCoefficientBlock, densePolynomial_coeff]

/-- Even zero and short inputs produce a complete, zero-padded block. -/
theorem denseCoefficientBlockCosted_length (read size block : ℕ) (values : List Fp) :
    (denseCoefficientBlockCosted read size block values).1.length = size :=
  ofFnCosted_length _

/-- The block budget includes failed reads beyond the stored coefficient range. -/
theorem denseCoefficientBlockCosted_cost_le (read size block : ℕ) (values : List Fp) :
    (denseCoefficientBlockCosted read size block values).2 ≤
      size * (2 * values.length + read + 4) + size * size + 1 := by
  apply ofFnCosted_cost_le (access := 2 * values.length + read + 3)
  intro index
  have h := getDListCosted_cost_le read (0 : Fp) values (size * block + index.val)
  dsimp only
  omega

/-- Materialize every block in the requested order. -/
@[irreducible] def denseCoefficientBlocksCosted (read size count : ℕ) (values : List Fp) : List (List Fp) × ℕ :=
  ofFnCosted fun block : Fin count => denseCoefficientBlockCosted read size block.val values

/-- Erasure preserves the original ordered family of coefficient blocks. -/
theorem denseCoefficientBlocksCosted_result (read size count : ℕ) (values : List Fp) :
    ((denseCoefficientBlocksCosted read size count values).1.map densePolynomial) =
      List.ofFn (fun block : Fin count => polynomialCoefficientBlock size block.val (densePolynomial values)) := by
  simp only [denseCoefficientBlocksCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    denseCoefficientBlockCosted_result]

/-- Every requested block is present in the result. -/
theorem denseCoefficientBlocksCosted_length (read size count : ℕ) (values : List Fp) :
    (denseCoefficientBlocksCosted read size count values).1.length = count := by
  unfold denseCoefficientBlocksCosted
  exact ofFnCosted_length _

/-- Every block is materialized at its complete declared width. -/
theorem denseCoefficientBlocksCosted_width (read size count : ℕ) (values piece : List Fp)
    (hpiece : piece ∈ (denseCoefficientBlocksCosted read size count values).1) : piece.length = size := by
  simp only [denseCoefficientBlocksCosted, ofFnCosted_result, List.mem_ofFn] at hpiece
  obtain ⟨index, rfl⟩ := hpiece
  exact denseCoefficientBlockCosted_length _ _ _ _

/-- Complete block collection includes every coefficient read and both levels of output storage. -/
theorem denseCoefficientBlocksCosted_cost_le (read size count : ℕ) (values : List Fp) :
    (denseCoefficientBlocksCosted read size count values).2 ≤
      count * (size * (2 * values.length + read + 4) + size * size + 2) + count * count + 1 := by
  unfold denseCoefficientBlocksCosted
  exact ofFnCosted_cost_le _ (size * (2 * values.length + read + 4) + size * size + 1)
    (fun block => denseCoefficientBlockCosted_cost_le read size block.val values)

end Zcash.Snark.ZeroKnowledge
