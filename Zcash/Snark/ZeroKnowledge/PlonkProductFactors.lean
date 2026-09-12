import Zcash.Snark.ZeroKnowledge.PlonkRowConstruction
import Zcash.Snark.ZeroKnowledge.ProductDenominatorLists

/-!
# The concrete lookup and permutation denominator factors

The lists below read the same column polynomials and key references as the actual
reference product scans. Every usable-row denominator factor occurs in these lists.
The counts retain duplicate factors and include all packed key references, so no
distinctness or copy-permutation correctness assumption is needed for the bound.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- The three beta-only lookup input factors on every usable row of every Action. -/
def plonkProductBetaOffsets {actions : ℕ} (rows : ColumnHistory 2048) : List Fp :=
  (List.finRange actions).flatMap fun a => (List.finRange 3).flatMap fun l =>
    (List.finRange 2042).map fun i =>
      (privateColumnPolynomial rows (.lookupInput a l)).eval (omegaOf 11 ^ i.val)

/-- All packed permutation factors, followed by the three gamma-only lookup table factors. -/
def plonkProductGammaForms {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (chunks : List (List (ColumnRef × ℕ))) : List (Fp × Fp) :=
  ((List.finRange actions).flatMap fun a => (List.finRange 2042).flatMap fun i =>
    (plonkPermutationPairPolynomials pub rows a chunks.flatten).map fun pair =>
      (pair.1.eval (omegaOf 11 ^ i.val), pair.2.eval (omegaOf 11 ^ i.val))) ++
  ((List.finRange actions).flatMap fun a => (List.finRange 3).flatMap fun l =>
    (List.finRange 2042).map fun i =>
      ((privateColumnPolynomial rows (.lookupTable a l)).eval (omegaOf 11 ^ i.val), 0))

/-- All product denominators used on usable rows are nonzero. -/
def plonkProductDenominatorsNonzero {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (chunks : List (List (ColumnRef × ℕ))) (beta gamma : Fp) : Prop :=
  (∀ a : Fin actions, ∀ c < chunks.length, ∀ i < 2042,
    permutationRowDenominator (plonkPermutationFactorRows pub rows a chunks) beta gamma c i ≠ 0) ∧
  ∀ (a : Fin actions) (l : Fin 3) (i : Fin 2042),
    (privateColumnPolynomial rows (.lookupInput a l)).eval (omegaOf 11 ^ i.val) + beta ≠ 0 ∧
    (privateColumnPolynomial rows (.lookupTable a l)).eval (omegaOf 11 ^ i.val) + gamma ≠ 0

/-- There are exactly `3m × 2042` beta-only factors. -/
theorem plonkProductBetaOffsets_length {actions : ℕ} (rows : ColumnHistory 2048) :
    (plonkProductBetaOffsets (actions := actions) rows).length = 3 * actions * 2042 := by
  simp [plonkProductBetaOffsets, List.length_flatMap, List.sum_replicate]
  omega

/-- Each packed key reference and each lookup contributes one gamma-linear factor per usable row. -/
theorem plonkProductGammaForms_length {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (chunks : List (List (ColumnRef × ℕ))) :
    (plonkProductGammaForms pub rows chunks).length = (chunks.flatten.length + 3) * actions * 2042 := by
  have hlength (a : Fin actions) (chunk : List (ColumnRef × ℕ)) :
      (plonkPermutationPairPolynomials pub rows a chunk).length = chunk.length := by
    simp only [plonkPermutationPairPolynomials, List.length_map]
  simp only [plonkProductGammaForms, List.length_append, List.length_flatMap,
    List.length_map, hlength, List.length_finRange, List.map_const', List.sum_replicate, nsmul_eq_mul,
    Nat.cast_id]
  ring

/-- Every actual lookup input factor is listed. -/
theorem plonkProductBetaOffsets_mem {actions : ℕ} (rows : ColumnHistory 2048)
    (a : Fin actions) (l : Fin 3) (i : Fin 2042) :
    (privateColumnPolynomial rows (.lookupInput a l)).eval (omegaOf 11 ^ i.val) ∈
      plonkProductBetaOffsets (actions := actions) rows := by
  simp only [plonkProductBetaOffsets, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  exact ⟨a, l, i, rfl⟩

/-- Every actual lookup table factor is listed with zero beta slope. -/
theorem plonkProductGammaForms_lookup_mem {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (chunks : List (List (ColumnRef × ℕ)))
    (a : Fin actions) (l : Fin 3) (i : Fin 2042) :
    ((privateColumnPolynomial rows (.lookupTable a l)).eval (omegaOf 11 ^ i.val), 0) ∈
      plonkProductGammaForms pub rows chunks := by
  unfold plonkProductGammaForms
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  exact ⟨a, l, i, rfl⟩

/-- Flattening the key preserves every actual permutation factor on every usable row. -/
theorem plonkProductGammaForms_permutation_mem {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (chunks : List (List (ColumnRef × ℕ)))
    (a : Fin actions) (c : ℕ) (hc : c < chunks.length) (i : Fin 2042) (pair : Fp × Fp)
    (hpair : pair ∈ plonkPermutationFactorRows pub rows a chunks c i.val) :
    pair ∈ plonkProductGammaForms pub rows chunks := by
  unfold plonkProductGammaForms
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨a, List.mem_finRange a, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  obtain ⟨polys, hpolys, rfl⟩ := List.mem_map.mp hpair
  apply List.mem_map.mpr
  refine ⟨polys, ?_, rfl⟩
  obtain ⟨ref, href, rfl⟩ := List.mem_map.mp hpolys
  apply List.mem_map.mpr
  refine ⟨ref, ?_, rfl⟩
  apply List.mem_flatten.mpr
  refine ⟨chunks.getD c [], ?_, href⟩
  rw [List.getD_eq_getElem _ _ hc]
  exact List.getElem_mem hc

/-- Avoiding the listed zero factors guarantees every actual product denominator is nonzero. -/
theorem plonkProductDenominatorsNonzero_of_not_listBad {actions : ℕ}
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (chunks : List (List (ColumnRef × ℕ))) (tape : ProductChallengeTape)
    (hgood : ¬ productDenominatorListBad (plonkProductBetaOffsets (actions := actions) rows)
      (plonkProductGammaForms pub rows chunks) tape) :
    plonkProductDenominatorsNonzero pub rows chunks (tape 0) (tape 1) := by
  constructor
  · intro a c hc i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hzero
    apply hgood
    apply Or.inr
    refine ⟨(plonkPermutationFactorRows pub rows a chunks c i).getD j (0, 0), ?_, hzero⟩
    apply plonkProductGammaForms_permutation_mem pub rows chunks a c hc ⟨i, hi⟩
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hj)]
    exact List.getElem_mem (Finset.mem_range.mp hj)
  · intro a l i
    constructor
    · intro hzero
      exact hgood (Or.inl ⟨_, plonkProductBetaOffsets_mem rows a l i, hzero⟩)
    · intro hzero
      apply hgood
      apply Or.inr
      refine ⟨_, plonkProductGammaForms_lookup_mem pub rows chunks a l i, ?_⟩
      simpa only [mul_zero, add_zero] using hzero

end Zcash.Snark.ZeroKnowledge
