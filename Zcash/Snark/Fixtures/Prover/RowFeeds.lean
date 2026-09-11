import Zcash.Snark.Fixtures.Prover.Polynomial

/-!
# Reading captured rows during private-column construction

At a domain point, the canonical interpolant returns the supplied row. The replay
uses this equality to read arrays directly, including advice rotations and the
query layout's out-of-range zero values.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Domain queries wrap after 2048 rows. -/
def domainRow (row : ℕ) : Fin 2048 := ⟨row % 2048, Nat.mod_lt _ (by decide)⟩

/-- Modular indexing preserves the evaluation point for every natural row index. -/
theorem domainRow_point (row : ℕ) : omegaOf 11 ^ row = omegaOf 11 ^ (domainRow row).val :=
  pow_eq_pow_mod _ (omegaOf_primitiveRoot 11 (by decide)).pow_eq_one

/-- Read one retained private column with the same missing-column default as the reference model. -/
def privateRow {actions : ℕ} (rows : ColumnHistory 2048) (id : PrivateColumnId actions)
    (row : Fin 2048) : Fp := (rows.getD (privateColumnIndex id).val 0) row

/-- A direct private read is the interpolated value, whether or not the column is present yet. -/
theorem privateRow_result {actions : ℕ} (rows : ColumnHistory 2048) (id : PrivateColumnId actions)
    (row : Fin 2048) : privateRow rows id row =
      (privateColumnPolynomial rows id).eval (omegaOf 11 ^ row.val) := by
  by_cases h : (privateColumnIndex id).val < rows.length
  · exact (privateColumnPolynomial_eval_row_of_present rows id h row).symm
  · change (rows.getD (privateColumnIndex id).val 0) row =
      ((rows.map (rowPolynomial (omegaOf 11))).getD (privateColumnIndex id).val 0).eval _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), Option.map_none, Option.getD_none,
      Pi.zero_apply, CPolynomial.eval_zero]

/-- Resolve advice queries to their actual current, next, or previous row. -/
def adviceFeed {actions : ℕ} (rows : ColumnHistory 2048) (a : Fin actions)
    (row : Fin 2048) : ℕ → Fp :=
  finFn fun query : Fin 25 => privateRow rows (.advice a (plonkAdviceQueryOrder query).1)
    (plonkAdviceRotationRow (plonkAdviceQueryOrder query).2 row)

/-- Direct advice reads give exactly the existing polynomial proof's advice feed. -/
theorem adviceFeed_result {actions : ℕ} (rows : ColumnHistory 2048) (a : Fin actions)
    (row : Fin 2048) : adviceFeed rows a row = plonkAdviceRowValues rows a row := by
  simp only [adviceFeed, privateRow_result, plonkAdviceRowValues]

/-- Read fixed values in the existing verifier's query order. -/
def fixedFeed (fixed : Fin 29 → Fin 2048 → Fp) (row : Fin 2048) : ℕ → Fp :=
  finFn fun query : Fin 29 => fixed (plonkFixedQueryOrder query) row

/-- The fixed feed returns the public interpolant's value at the selected row. -/
theorem fixedFeed_result {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) (row : Fin 2048) :
    fixedFeed fixed row = plonkFixedRowValues (plonkPublicPolynomialsFromRows instances fixed sigma) row :=
  (plonkPublicPolynomialsFromRows_fixedRowValues instances fixed sigma row).symm

/-- Each Action has one instance column, with zero for any other query index. -/
def instanceFeed {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp) (a : Fin actions)
    (row : Fin 2048) : ℕ → Fp := finFn fun _ : Fin 1 => instances a row

/-- Direct instance reads preserve the reference polynomial query and its zero default. -/
theorem instanceFeed_result {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (a : Fin actions) (row : Fin 2048) :
    instanceFeed instances a row =
      plonkInstanceRowValues (plonkPublicPolynomialsFromRows instances fixed sigma) a row := by
  simp only [instanceFeed, plonkInstanceRowValues, plonkPublicPolynomialsFromRows_instances_eval]

/-- Compress a lookup expression tuple using the actual public and previously masked private rows. -/
def lookupValues {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (rows : ColumnHistory 2048) (theta : Fp)
    (a : Fin actions) (exprs : List (Expr Fp)) (row : ℕ) : Fp :=
  compressExprs (fixedFeed fixed (domainRow row)) (adviceFeed rows a (domainRow row))
    (instanceFeed instances a (domainRow row)) theta exprs

/-- Lookup compression agrees for every row, including modular wraparound. -/
theorem lookupValues_result {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (theta : Fp) (a : Fin actions)
    (exprs : List (Expr Fp)) (row : ℕ) :
    lookupValues instances fixed rows theta a exprs row =
      plonkLookupCompressedRows (plonkPublicPolynomialsFromRows instances fixed sigma)
        rows theta a exprs row := by
  unfold lookupValues plonkLookupCompressedRows
  rw [domainRow_point row]
  simp only [plonkPolynomialClaimProof_fixedRowValues, plonkPolynomialClaimProof_adviceRowValues,
    plonkPolynomialClaimProof_instanceRowValues, fixedFeed_result instances fixed sigma,
    adviceFeed_result, instanceFeed_result instances fixed sigma]

/-- Resolve permutation column and sigma references directly on the selected domain row. -/
def permutationPairs {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (chunk row : ℕ) : List (Fp × Fp) :=
  let r := domainRow row
  (chunks.getD chunk []).map fun cr =>
    (cr.1.resolve (instanceFeed instances a r) (adviceFeed rows a r) (fixedFeed fixed r),
      finFn (fun c : Fin 15 => sigma c r) cr.2)

/-- Polynomial evaluation commutes with the packed column selector used by permutation chunks. -/
private theorem resolve_eval (ref : ColumnRef) (instances advice fixed : ℕ → CPoly) (point : Fp) :
    (ref.resolve instances advice fixed).eval point =
      ref.resolve (fun i => (instances i).eval point) (fun i => (advice i).eval point)
        (fun i => (fixed i).eval point) := by
  cases ref <;> rfl

/-- Direct permutation reads retain both the value and sigma label of every original factor. -/
theorem permutationPairs_result {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (chunk row : ℕ) :
    permutationPairs instances fixed sigma rows a chunks chunk row =
      plonkPermutationFactorRows (plonkPublicPolynomialsFromRows instances fixed sigma)
        rows a chunks chunk row := by
  unfold permutationPairs plonkPermutationFactorRows plonkPermutationPairPolynomials
  simp only [List.map_map]
  apply List.map_congr_left
  intro cr _
  dsimp only [Function.comp_def]
  apply Prod.ext
  · rw [resolve_eval, domainRow_point row]
    simp only [plonkPolynomialClaimProof_fixedRowValues, plonkPolynomialClaimProof_adviceRowValues,
      plonkPolynomialClaimProof_instanceRowValues, fixedFeed_result instances fixed sigma,
      adviceFeed_result, instanceFeed_result instances fixed sigma]
  · simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString]
    rw [domainRow_point row]
    change finFn (fun c : Fin 15 => sigma c (domainRow row)) cr.2 =
      (finFn (plonkPublicPolynomialsFromRows instances fixed sigma).sigma cr.2).eval
        (omegaOf 11 ^ (domainRow row).val)
    by_cases h : cr.2 < 15
    · simp only [finFn, dif_pos h, plonkPublicPolynomialsFromRows_sigma_eval]
    · simp [finFn, h]

end Zcash.Snark.Fixtures.Prover
