import Zcash.Snark.ZeroKnowledge.PlonkConstraints
import Zcash.Snark.ZeroKnowledge.LookupRowConstraints

/-!
# Canonical selectors on the row domain

The polynomial selector triple used by the honest constraint numerator evaluates to
the first-row, terminal-row, and blinding-row indicators used in the row algorithms.
The fixed 2048-row specialization uses the kernel-checked root-of-unity certificate.
This covers domain points directly; the off-domain rational selector formula is not used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- Canonical selector polynomials give the three row indicators. -/
theorem canonicalLagrangePolynomials_eval_row {n blinding : ℕ}
    (omega : Fp) (hblinding : blinding < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val) (row : Fin n) :
    let selectors := canonicalLagrangePolynomials omega hblinding
    (selectors.1.eval (omega ^ row.val), selectors.2.1.eval (omega ^ row.val),
      selectors.2.2.eval (omega ^ row.val)) =
        rowSelectorValues (F := Fp) (n - blinding - 1) row.val := by
  have hrow (selected : Fin n) := rowSelectorPolynomial_eval selected row hrows
  have hblind (last : Fin n) := blindSelectorPolynomial_eval last row hrows
  simp only [canonicalLagrangePolynomials, hrow, hblind, rowSelectorValues,
    Fin.ext_iff, lastUsableDomainRow]

/-- The actual numerator's selectors retain row 2042 and mask the five following rows. -/
theorem plonkSelectors_eval_row (row : Fin 2048) :
    (plonkSelectors.1.eval (omegaOf 11 ^ row.val), plonkSelectors.2.1.eval (omegaOf 11 ^ row.val),
      plonkSelectors.2.2.eval (omegaOf 11 ^ row.val)) =
        rowSelectorValues (F := Fp) 2042 row.val := by
  unfold plonkSelectors
  exact canonicalLagrangePolynomials_eval_row (omegaOf 11) (by decide : 5 < 2048)
    (omegaOf_rows_injective 11 (by decide)) row

end Zcash.Snark.ZeroKnowledge
