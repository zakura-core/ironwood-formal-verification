import Zcash.Snark.ZeroKnowledge.DensePolynomialDivision

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Successive monic polynomial divisions give the quotient by the product, including nonzero remainders. -/
theorem polynomial_divByMonic_product (p g h : Polynomial Fp) (hg : g.Monic) (hh : h.Monic) :
    (p /ₘ g) /ₘ h = p /ₘ (g * h) := by
  have dg : g.degree = (g.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hg.ne_zero
  have dh : h.degree = (h.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hh.ne_zero
  have hr : (p %ₘ g + g * ((p /ₘ g) %ₘ h)).degree < (g * h).degree := by
    apply (Polynomial.degree_add_le _ _).trans_lt
    apply max_lt_iff.mpr
    constructor
    · apply (Polynomial.degree_modByMonic_lt p hg).trans_le
      simp only [Polynomial.degree_mul, dg, dh]
      exact_mod_cast (Nat.le_add_right g.natDegree h.natDegree)
    · by_cases hz : (p /ₘ g) %ₘ h = 0
      · simp [hz, Polynomial.degree_mul, dg, dh]
      · have hm := Polynomial.degree_modByMonic_lt (p /ₘ g) hh
        rw [Polynomial.degree_eq_natDegree hz, dh] at hm
        have hn : ((p /ₘ g) %ₘ h).natDegree < h.natDegree := by exact_mod_cast hm
        simp only [Polynomial.degree_mul, dg, dh, Polynomial.degree_eq_natDegree hz]
        exact_mod_cast (Nat.add_lt_add_left hn g.natDegree)
  have hi : p %ₘ g + g * ((p /ₘ g) %ₘ h) + (g * h) * ((p /ₘ g) /ₘ h) = p := by
    calc
      _ = p %ₘ g + g * ((p /ₘ g) %ₘ h + h * ((p /ₘ g) /ₘ h)) := by ring
      _ = p %ₘ g + g * (p /ₘ g) := by rw [Polynomial.modByMonic_add_div]
      _ = p := Polynomial.modByMonic_add_div p g
  exact (Polynomial.div_modByMonic_unique ((p /ₘ g) /ₘ h)
    (p %ₘ g + g * ((p /ₘ g) %ₘ h)) (hg.mul hh) ⟨hi, hr⟩).1.symm

/-- The same composition law holds for the field-polynomial quotient used by the source. -/
theorem polynomial_div_product_monic (p g h : Polynomial Fp) (hg : g.Monic) (hh : h.Monic) :
    (p / g) / h = p / (g * h) := by
  have hm := polynomial_divByMonic_product p g h hg hh
  simpa only [Polynomial.divByMonic_eq_div p hg,
    Polynomial.divByMonic_eq_div (p / g) hh, Polynomial.divByMonic_eq_div p (hg.mul hh)] using hm

/-- Canonical executable polynomial division preserves successive monic quotients. -/
theorem cPolynomial_div_product_monic (p g h : CPoly) (hg : g.toPoly.Monic) (hh : h.toPoly.Monic) :
    (p.div g).div h = p.div (g * h) := by
  apply CPolynomial.toPoly_injective
  simp only [CPolynomial.div_toPoly_eq_div, CPolynomial.toPoly_mul]
  exact polynomial_div_product_monic _ _ _ hg hh

end Zcash.Snark.ZeroKnowledge
