import Zcash.Snark.ZeroKnowledge.DenseRootDivision
import Zcash.Snark.ZeroKnowledge.DomainDivisibility
import Zcash.Snark.ZeroKnowledge.QuotientPieces

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Materialize every actual domain root with its full generator and exponentiation cost. -/
def domainRootsCosted (multiply omegaAccess k : ℕ) : List Fp × ℕ :=
  ofFnCosted fun index : Fin (2 ^ k) =>
    let power := fieldPowerCosted multiply (omegaOf k) index.val
    (power.1, omegaAccess + power.2 + 1)

/-- The stored root order is exactly the original domain enumeration. -/
theorem domainRootsCosted_result (multiply omegaAccess k : ℕ) :
    (domainRootsCosted multiply omegaAccess k).1 = List.ofFn (fun i : Fin (2 ^ k) => omegaOf k ^ i.val) := by
  simp only [domainRootsCosted, ofFnCosted_result, fieldPowerCosted_result]

/-- The materialized root vector has the full declared domain size. -/
theorem domainRootsCosted_length (multiply omegaAccess k : ℕ) :
    (domainRootsCosted multiply omegaAccess k).1.length = 2 ^ k := by
  rw [domainRootsCosted_result, List.length_ofFn]

/-- Root preparation charges every exponentiation and every output cell. -/
theorem domainRootsCosted_cost_le (multiply omegaAccess k : ℕ) :
    (domainRootsCosted multiply omegaAccess k).2 ≤
      (2 ^ k) * (omegaAccess + (2 ^ k) * (multiply + 1) + 3) + (2 ^ k) * (2 ^ k) + 1 := by
  apply ofFnCosted_cost_le (access := omegaAccess + (2 ^ k) * (multiply + 1) + 2)
  intro index
  dsimp only
  rw [fieldPowerCosted_cost]
  have h := Nat.mul_le_mul_right (multiply + 1) (Nat.le_of_lt index.isLt)
  omega

/-- The actual root-factor product is the original row-domain divisor. -/
theorem denseRootDivisor_domain (k : ℕ) (hk : k ≤ 32) :
    denseRootDivisor (List.ofFn (fun i : Fin (2 ^ k) => omegaOf k ^ i.val)) =
      CPolynomial.X ^ (2 ^ k) - 1 := by
  apply CPolynomial.toPoly_injective
  simp only [denseRootDivisor, List.map_ofFn, Function.comp_def, List.prod_ofFn, CPolynomial.toPoly_prod,
    CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly,
    CPolynomial.toPoly_pow, CPolynomial.toPoly_one]
  exact (rowDomain_product (omegaOf k) (Nat.two_pow_pos k) (omegaOf_primitiveRoot k hk)).symm

/-- Execute the full row-domain quotient without a divisibility assumption. -/
@[irreducible] def denseDomainQuotientCosted (read add multiply omegaAccess k : ℕ) (values : List Fp) : List Fp × ℕ :=
  let roots := domainRootsCosted multiply omegaAccess k
  let quotient := denseDivRootsCosted read add multiply roots.1 values
  (quotient.1, roots.2 + quotient.2 + 1)

/-- The stored algorithm returns exactly the source's executable domain quotient on all numerators. -/
theorem denseDomainQuotientCosted_result (read add multiply omegaAccess k : ℕ) (hk : k ≤ 32)
    (values : List Fp) :
    densePolynomial (denseDomainQuotientCosted read add multiply omegaAccess k values).1 =
      domainQuotient (2 ^ k) (densePolynomial values) := by
  rw [denseDomainQuotientCosted, denseDivRootsCosted_result, domainRootsCosted_result, denseRootDivisor_domain k hk]
  rfl

/-- Domain division retains the input's coefficient storage bound. -/
theorem denseDomainQuotientCosted_length (read add multiply omegaAccess k : ℕ) (values : List Fp) :
    (denseDomainQuotientCosted read add multiply omegaAccess k values).1.length = values.length := by
  unfold denseDomainQuotientCosted
  exact denseDivRootsCosted_length _ _ _ _ _

/-- The complete quotient budget includes domain-root construction and every synthetic-division pass. -/
theorem denseDomainQuotientCosted_cost_le (read add multiply omegaAccess k : ℕ) (values : List Fp) :
    (denseDomainQuotientCosted read add multiply omegaAccess k values).2 ≤
      (2 ^ k) * (omegaAccess + (2 ^ k) * (multiply + 1) +
        values.length * (read + add + multiply + 5) + read + 8) + (2 ^ k) * (2 ^ k) + 3 := by
  have hr := domainRootsCosted_cost_le multiply omegaAccess k
  have hd := denseDivRootsCosted_cost read add multiply (domainRootsCosted multiply omegaAccess k).1 values
  rw [domainRootsCosted_length] at hd
  unfold denseDomainQuotientCosted
  dsimp only
  rw [hd]
  calc
    _ ≤ ((2 ^ k) * (omegaAccess + (2 ^ k) * (multiply + 1) + 3) + (2 ^ k) * (2 ^ k) + 1) +
        ((2 ^ k) * (values.length * (read + add + multiply + 5) + read + 5) + 1) + 1 := by omega
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
