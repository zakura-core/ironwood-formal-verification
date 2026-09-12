import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.VectorCommitmentCost
import Zcash.Snark.ZeroKnowledge.ListIndexCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Commit directly from stored coefficients; semantic polynomial decoding is absent from execution. -/
def densePolynomialCommitmentCosted (read groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : List Fp × ℕ) (blind : Fp × ℕ) : G × ℕ :=
  let commitment := vectorCommitmentCosted groupAdd groupScale generators
    (fun index => getDListCosted read (0 : Fp) poly.1 index.val)
  (commitment.1 + blind.1 • W.1,
    poly.2 + commitment.2 + blind.2 + W.2 + groupScale + groupAdd + 1)

/-- Stored coefficient reads give the original polynomial commitment, including every defaulted coefficient. -/
theorem densePolynomialCommitmentCosted_result (read groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : List Fp × ℕ) (blind : Fp × ℕ) :
    (densePolynomialCommitmentCosted read groupAdd groupScale generators W poly blind).1 =
      polynomialCommitment (fun index => (generators index).1) W.1 (densePolynomial poly.1) blind.1 := by
  simp only [densePolynomialCommitmentCosted, vectorCommitmentCosted_result, getDListCosted_result,
    polynomialCommitment, commitGen, Zcash.Snark.ZeroKnowledge.polynomialCoefficients, densePolynomial_coeff]

/-- Complete stored-coefficient commitment budget, including the polynomial producer and full generator sweep. -/
def densePolynomialCommitmentCostBudget
    (read groupAdd groupScale n width generatorRead polynomialRead blindRead wRead : ℕ) : ℕ :=
  polynomialRead + blindRead + wRead +
    n * (2 * width + read + 1 + generatorRead + groupScale + groupAdd + 2) +
    n * n + groupScale + groupAdd + 2

/-- Every stored coefficient traversal and supplied input cost enters the commitment bound. -/
theorem densePolynomialCommitmentCosted_cost_le (read groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : List Fp × ℕ) (blind : Fp × ℕ)
    (generatorRead : ℕ) (hg : ∀ index, (generators index).2 ≤ generatorRead) :
    (densePolynomialCommitmentCosted read groupAdd groupScale generators W poly blind).2 ≤
      densePolynomialCommitmentCostBudget read groupAdd groupScale n poly.1.length generatorRead poly.2 blind.2 W.2 := by
  have h := vectorCommitmentCosted_cost_le groupAdd groupScale generators
    (fun index => getDListCosted read (0 : Fp) poly.1 index.val) generatorRead
    (2 * poly.1.length + read + 1) hg
    (fun index => getDListCosted_cost_le read (0 : Fp) poly.1 index.val)
  change poly.2 + (vectorCommitmentCosted groupAdd groupScale generators
    (fun index => getDListCosted read (0 : Fp) poly.1 index.val)).2 +
      blind.2 + W.2 + groupScale + groupAdd + 1 ≤ _
  unfold densePolynomialCommitmentCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
