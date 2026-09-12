import Zcash.Snark.ZeroKnowledge.ColumnRetained
import Zcash.Snark.ZeroKnowledge.PlonkPrefix
import Zcash.Snark.ZeroKnowledge.PlonkConstructedRows

/-!
# Original advice and its retained rows in the total reference prover

The comparison state below contains the supplied advice rows and zeros in the other
private-column slots. It is an analysis input, not a prover transcript. The actual
masked construction agrees with these advice polynomials on every usable row, for
every tape and every challenge record, without assuming successful lookup sorting.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- The original advice in the fixed column positions, with zero placeholders for all other columns. -/
def plonkUnmaskedAdviceRows {actions : ℕ} (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    ColumnHistory 2048 :=
  (privateColumnOrder actions).map fun id => match id with
    | .advice a c => witness a c
    | _ => 0

/-- A private advice column in the comparison state is exactly its original row polynomial. -/
theorem plonkUnmaskedAdviceRows_polynomial {actions : ℕ}
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (a : Fin actions) (c : Fin 10) :
    privateColumnPolynomial (plonkUnmaskedAdviceRows witness) (.advice a c) =
      rowPolynomial (omegaOf 11) (witness a c) := by
  have hindex : (privateColumnIndex (.advice a c)).val < (plonkUnmaskedAdviceRows witness).length := by
    simpa only [plonkUnmaskedAdviceRows, List.length_map, privateColumnOrder_length] using
      (privateColumnIndex (.advice a c)).isLt
  change ((plonkUnmaskedAdviceRows witness).map (rowPolynomial (omegaOf 11))).getD
    (privateColumnIndex (.advice a c)).val 0 = _
  rw [List.getD_eq_getElem _ 0 (by simpa only [List.length_map] using hindex), List.getElem_map]
  simp [plonkUnmaskedAdviceRows, privateColumnIndex, List.getElem_map]

/-- The original advice polynomial evaluates to the supplied cell on the complete domain. -/
theorem plonkUnmaskedAdviceRows_eval {actions : ℕ}
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (a : Fin actions) (c : Fin 10) (i : Fin 2048) :
    (privateColumnPolynomial (plonkUnmaskedAdviceRows witness) (.advice a c)).eval (omegaOf 11 ^ i.val) =
      witness a c i := by
  rw [plonkUnmaskedAdviceRows_polynomial, rowPolynomial_eval (omegaOf_rows_injective 11 (by decide))]

/-- Every usable advice cell survives the total construction, independently of later sort failures. -/
theorem plonkTotalColumnRows_advice_rows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) (c : Fin 10)
    (i : Fin 2048) (hi : i.val < 2042) :
    (privateColumnPolynomial (plonkTotalColumnRows vk pub witness ch tape) (.advice a c)).eval
      (omegaOf 11 ^ i.val) = witness a c i := by
  let construct := plonkTotalColumnConstructor vk pub witness ch
  have hindex : (privateColumnIndex (.advice a c)).val < (plonkColumnSteps construct).length := by
    rw [plonkColumnSteps_length]
    exact (privateColumnIndex (.advice a c)).isLt
  have hstep : (plonkColumnSteps construct)[(privateColumnIndex (.advice a c)).val] =
      (⟨2042, construct (.advice a c)⟩ : ColumnStep 2048) := by
    simp [plonkColumnSteps, privateColumnIndex, List.getElem_map, PrivateColumnId.firstMasked]
  have hkeep := columnRowsFromTape_retained (plonkColumnSteps construct) []
    (tape ∘ Fin.cast (plonkColumnSteps_row_samples construct))
    (privateColumnIndex (.advice a c)).val hindex i (by simpa only [hstep] using hi)
  rw [hstep] at hkeep
  rw [privateColumnPolynomial_eval_row_of_present _ _
    (by rw [plonkTotalColumnRows_length]; exact (privateColumnIndex (.advice a c)).isLt)]
  exact hkeep

end Zcash.Snark.ZeroKnowledge
