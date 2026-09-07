import Zcash.Snark.ZeroKnowledge.PlonkExpressionRows

/-!
# Public row vectors determine the reference public polynomials

The instance, fixed, and sigma polynomials are the existing interpolants of their
2048-row vectors. Their degree bounds and every domain evaluation follow from
interpolation, rather than being separate premises about arbitrary polynomials.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- Construct the public polynomials from their domain-row vectors. -/
def plonkPublicPolynomialsFromRows {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) : PlonkPublicPolynomials actions where
  instances a := rowPolynomial (omegaOf 11) (instances a)
  fixed c := rowPolynomial (omegaOf 11) (fixed c)
  sigma c := rowPolynomial (omegaOf 11) (sigma c)

/-- Each public instance polynomial evaluates to its supplied row value. -/
theorem plonkPublicPolynomialsFromRows_instances_eval {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (a : Fin actions) (row : Fin 2048) :
    ((plonkPublicPolynomialsFromRows instances fixed sigma).instances a).eval
      (omegaOf 11 ^ row.val) = instances a row := by
  simp only [plonkPublicPolynomialsFromRows]
  exact rowPolynomial_eval (values := instances a) (omegaOf_rows_injective 11 (by decide)) row

/-- Each public fixed polynomial evaluates to its supplied row value. -/
theorem plonkPublicPolynomialsFromRows_fixed_eval {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (c : Fin 29) (row : Fin 2048) :
    ((plonkPublicPolynomialsFromRows instances fixed sigma).fixed c).eval
      (omegaOf 11 ^ row.val) = fixed c row := by
  simp only [plonkPublicPolynomialsFromRows]
  exact rowPolynomial_eval (values := fixed c) (omegaOf_rows_injective 11 (by decide)) row

/-- Each public permutation polynomial evaluates to its supplied row label. -/
theorem plonkPublicPolynomialsFromRows_sigma_eval {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (c : Fin 15) (row : Fin 2048) :
    ((plonkPublicPolynomialsFromRows instances fixed sigma).sigma c).eval
      (omegaOf 11 ^ row.val) = sigma c row := by
  simp only [plonkPublicPolynomialsFromRows]
  exact rowPolynomial_eval (values := sigma c) (omegaOf_rows_injective 11 (by decide)) row

/-- The public row construction supplies every degree bound used by the simulation. -/
theorem plonkPublicPolynomialsFromRows_degree {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) :
    (∀ a, ((plonkPublicPolynomialsFromRows instances fixed sigma).instances a).natDegree < 2048) ∧
    (∀ c, ((plonkPublicPolynomialsFromRows instances fixed sigma).fixed c).natDegree < 2048) ∧
    (∀ c, ((plonkPublicPolynomialsFromRows instances fixed sigma).sigma c).natDegree < 2048) := by
  simp only [plonkPublicPolynomialsFromRows]
  exact ⟨fun a => rowPolynomial_natDegree_lt (values := instances a)
      (omegaOf_rows_injective 11 (by decide)) (by decide),
    fun c => rowPolynomial_natDegree_lt (values := fixed c)
      (omegaOf_rows_injective 11 (by decide)) (by decide),
    fun c => rowPolynomial_natDegree_lt (values := sigma c)
      (omegaOf_rows_injective 11 (by decide)) (by decide)⟩

/-- The verifier's fixed-query feed is the same row vector in the pinned query order. -/
theorem plonkPublicPolynomialsFromRows_fixedRowValues {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (row : Fin 2048) :
    plonkFixedRowValues (plonkPublicPolynomialsFromRows instances fixed sigma) row =
      finFn (fun query : Fin 29 => fixed (plonkFixedQueryOrder query) row) := by
  funext query
  by_cases hquery : query < 29
  · simp only [plonkFixedRowValues, finFn, hquery, ↓reduceDIte]
    exact plonkPublicPolynomialsFromRows_fixed_eval instances fixed sigma _ row
  · simp [plonkFixedRowValues, finFn, hquery]

end Zcash.Snark.ZeroKnowledge
