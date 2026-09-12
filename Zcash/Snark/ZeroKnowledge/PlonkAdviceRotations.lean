import Zcash.Snark.ZeroKnowledge.PlonkAdviceRows

/-!
# Retained advice queries at rotated domain rows

The pinned advice query layout uses the current, next, and previous rows. Rotation
wraps modulo 2048; a query is retained exactly when its target row is below 2042.
Out-of-range query indices resolve to zero and are also invariant. The statements
use the actual polynomial query constructor and the kernel root certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Nonnegative representatives of the three advice rotations modulo 2048. -/
def plonkAdviceRotationOffsets : Fin 3 → ℕ := ![0, 1, 2047]

/-- The row read by an advice rotation, including wraparound at either domain boundary. -/
def plonkAdviceRotationRow (rotation : Fin 3) (row : Fin 2048) : Fin 2048 :=
  ⟨(row.val + plonkAdviceRotationOffsets rotation) % 2048, Nat.mod_lt _ (by decide)⟩

/-- A public query check identifying exactly the advice values retained by suffix masking. -/
def plonkAdviceQueryRetained (row : Fin 2048) (query : ℕ) : Bool :=
  if h : query < 25 then
    decide ((plonkAdviceRotationRow (plonkAdviceQueryOrder ⟨query, h⟩).2 row).val < 2042)
  else true

/-- The polynomial rotation factor reads the corresponding modular row. -/
theorem plonkAdviceQueryFactor_row (rotation : Fin 3) (row : Fin 2048) :
    plonkQueryFactors (rotation.castLE (by decide)) * omegaOf 11 ^ row.val =
      omegaOf 11 ^ (plonkAdviceRotationRow rotation row).val := by
  have hroot : omegaOf 11 ^ 2048 = 1 := (omegaOf_primitiveRoot 11 (by decide)).pow_eq_one
  have hfactor : plonkQueryFactors (rotation.castLE (by decide)) =
      omegaOf 11 ^ plonkAdviceRotationOffsets rotation := by
    fin_cases rotation
    · simp [plonkQueryFactors, plonkAdviceRotationOffsets]
    · simp [plonkQueryFactors, plonkAdviceRotationOffsets]
    · change (omegaOf 11)⁻¹ = omegaOf 11 ^ 2047
      apply inv_eq_of_mul_eq_one_left
      simpa only [← pow_succ] using hroot
  rw [hfactor, ← pow_add, Nat.add_comm]
  exact pow_eq_pow_mod _ hroot

/-- A polynomial advice query at a domain row evaluates at its actual rotated row. -/
theorem plonkPolynomialClaimProof_advice_eval_row {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (a : Fin actions)
    (query : Fin 25) (row : Fin 2048) :
    ((plonkPolynomialClaimProof (k := k) (G := G) pub rows).adviceEvals a query).eval (omegaOf 11 ^ row.val) =
      (privateColumnPolynomial rows (.advice a (plonkAdviceQueryOrder query).1)).eval
        (omegaOf 11 ^ (plonkAdviceRotationRow (plonkAdviceQueryOrder query).2 row).val) := by
  change (plonkRotatedColumn rows (.advice a (plonkAdviceQueryOrder query).1)
    ((plonkAdviceQueryOrder query).2.castLE (by decide))).eval _ = _
  simp only [plonkRotatedColumn, CPolynomial.eval_comp, CPolynomial.eval_mul,
    CPolynomial.eval_C, CPolynomial.eval_X, plonkAdviceQueryFactor_row]

/-- The concrete advice-query valuation at a domain row, with the verifier's zero fallback. -/
def plonkAdviceRowValues {actions : ℕ} (rows : ColumnHistory 2048) (a : Fin actions)
    (row : Fin 2048) : ℕ → Fp :=
  finFn fun query : Fin 25 =>
    (privateColumnPolynomial rows (.advice a (plonkAdviceQueryOrder query).1)).eval
      (omegaOf 11 ^ (plonkAdviceRotationRow (plonkAdviceQueryOrder query).2 row).val)

/-- The row valuation is exactly the advice feed of the existing polynomial proof. -/
theorem plonkPolynomialClaimProof_adviceRowValues {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (a : Fin actions)
    (row : Fin 2048) (query : ℕ) :
    (finFn ((plonkPolynomialClaimProof (k := k) (G := G) pub rows).adviceEvals a) query).eval
        (omegaOf 11 ^ row.val) = plonkAdviceRowValues rows a row query := by
  by_cases hq : query < 25
  · have hshape : query < (plonkProofShape actions k).numAdviceQueries := hq
    simp only [plonkAdviceRowValues, finFn, dif_pos hshape, dif_pos hq]
    exact plonkPolynomialClaimProof_advice_eval_row pub rows a ⟨query, hq⟩ row
  · have hshape : ¬ query < (plonkProofShape actions k).numAdviceQueries := hq
    simp only [plonkAdviceRowValues, finFn, dif_neg hshape, dif_neg hq, CPolynomial.eval_zero]

/-- Every retained query has its original value on every total-construction tape. -/
theorem plonkAdviceRowValues_masked {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) (row : Fin 2048) (query : ℕ)
    (hretained : plonkAdviceQueryRetained row query = true) :
    plonkAdviceRowValues (plonkTotalColumnRows vk pub witness ch tape) a row query =
      plonkAdviceRowValues (plonkUnmaskedAdviceRows witness) a row query := by
  by_cases hq : query < 25
  · have hrow : (plonkAdviceRotationRow (plonkAdviceQueryOrder ⟨query, hq⟩).2 row).val < 2042 := by
      simpa only [plonkAdviceQueryRetained, dif_pos hq, decide_eq_true_eq] using hretained
    simp only [plonkAdviceRowValues, finFn, dif_pos hq]
    exact (plonkTotalColumnRows_advice_rows vk pub witness ch tape a
      (plonkAdviceQueryOrder ⟨query, hq⟩).1 _ hrow).trans
        (plonkUnmaskedAdviceRows_eval witness a (plonkAdviceQueryOrder ⟨query, hq⟩).1 _).symm
  · simp only [plonkAdviceRowValues, finFn, dif_neg hq]

end Zcash.Snark.ZeroKnowledge
