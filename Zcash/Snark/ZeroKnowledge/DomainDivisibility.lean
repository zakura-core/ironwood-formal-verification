import Zcash.Snark.ZeroKnowledge.PlonkConstraints
import Mathlib.FieldTheory.KummerExtension

/-!
# From row constraints to exact domain division

A polynomial vanishes at every row of a root-of-unity domain exactly when the domain
polynomial divides it. This supplies the computed quotient's divisibility premise from
row-wise correctness, without assuming a quotient identity or constructing a quotient
witness externally. The row algorithms that establish correctness remain separate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- The primitive row domain's vanishing polynomial is its product of distinct row factors. -/
theorem rowDomain_product {n : ℕ} (omega : Fp) (hn : 0 < n) (hroot : IsPrimitiveRoot omega n) :
    (Polynomial.X ^ n - (1 : Polynomial Fp)) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (omega ^ i.val)) := by
  have h := X_pow_sub_C_eq_prod hroot hn (one_pow n : (1 : Fp) ^ n = 1)
  rw [Fin.prod_univ_eq_prod_range (fun i => Polynomial.X - Polynomial.C (omega ^ i)) n]
  simpa only [Polynomial.C_1, mul_one] using h

/-- Vanishing at all domain rows gives exact divisibility, with no degree restriction. -/
theorem domainPolynomial_dvd_of_rows {n : ℕ} (omega : Fp) (hn : 0 < n)
    (hroot : IsPrimitiveRoot omega n) (poly : CPoly)
    (hrows : ∀ i : Fin n, poly.eval (omega ^ i.val) = 0) :
    (CPolynomial.X ^ n - 1 : CPoly) ∣ poly := by
  rw [CPolynomial.dvd_iff_toPoly_dvd, CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.toPoly_one, rowDomain_product omega hn hroot]
  have hinjective : Function.Injective (fun i : Fin n => omega ^ i.val) := by
    intro i j hij
    exact Fin.ext (hroot.pow_inj i.isLt j.isLt hij)
  apply Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hinjective)
  intro i
  apply Polynomial.dvd_iff_isRoot.mpr
  exact (CPolynomial.eval_toPoly (omega ^ i.val) poly).symm.trans (hrows i)

/-- Exact domain divisibility forces every row evaluation to vanish. -/
theorem rows_zero_of_domainPolynomial_dvd {n : ℕ} (omega : Fp) (hroot : omega ^ n = 1)
    (poly : CPoly) (hdiv : (CPolynomial.X ^ n - 1 : CPoly) ∣ poly) (i : Fin n) :
    poly.eval (omega ^ i.val) = 0 := by
  obtain ⟨quotient, hquotient⟩ := hdiv
  have hpow : (omega ^ i.val) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  rw [hquotient, CPolynomial.eval_mul, CPolynomial.eval_sub, CPolynomial.eval_pow,
    CPolynomial.eval_X, CPolynomial.eval_one, hpow, sub_self, zero_mul]

/-- The two equivalent forms of row-domain correctness. -/
theorem domainPolynomial_dvd_iff_rows {n : ℕ} (omega : Fp) (hn : 0 < n)
    (hroot : IsPrimitiveRoot omega n) (poly : CPoly) :
    (CPolynomial.X ^ n - 1 : CPoly) ∣ poly ↔
      ∀ i : Fin n, poly.eval (omega ^ i.val) = 0 :=
  ⟨fun hdiv => rows_zero_of_domainPolynomial_dvd omega hroot.pow_eq_one poly hdiv,
    domainPolynomial_dvd_of_rows omega hn hroot poly⟩

/-- A Horner fold of constraints vanishing at a point still vanishes there. -/
theorem plonkPolynomialFold_eval_zero (challenge x : Fp) (polys : List CPoly)
    (hpolys : ∀ poly ∈ polys, poly.eval x = 0) :
    (plonkPolynomialFold challenge polys).eval x = 0 := by
  have h (acc : CPoly) (hacc : acc.eval x = 0) :
      (polys.foldl (fun acc poly => acc * CPolynomial.C challenge + poly) acc).eval x = 0 := by
    induction polys generalizing acc with
    | nil => exact hacc
    | cons poly rest ih =>
      rw [List.foldl_cons]
      apply ih (fun p hp => hpolys p (List.mem_cons_of_mem poly hp))
      rw [CPolynomial.eval_add, CPolynomial.eval_mul, hacc,
        hpolys poly (List.mem_cons_self ..), zero_mul, zero_add]
  exact h 0 (CPolynomial.eval_zero x)

/-- Row correctness of every constraint derives divisibility of the actual numerator. -/
theorem plonkConstraintNumerator_dvd_of_rows {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048)
    (hrows : ∀ poly ∈ (plonkConstraintModel vk pub ch rows).constraints,
      ∀ i : Fin 2048, poly.eval (omegaOf 11 ^ i.val) = 0) :
    (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows := by
  apply domainPolynomial_dvd_of_rows (omegaOf 11) (by decide)
    (omegaOf_primitiveRoot 11 (by decide))
  intro i
  rw [plonkConstraintNumerator_eq_fold]
  exact plonkPolynomialFold_eval_zero ch.y (omegaOf 11 ^ i.val)
    (plonkConstraintModel vk pub ch rows).constraints (fun poly hpoly => hrows poly hpoly i)

end Zcash.Snark.ZeroKnowledge
