import Zcash.Snark.ZeroKnowledge.PlonkColumnReads
import Zcash.Snark.ZeroKnowledge.PlonkConstruction

/-!
# Completed column attempts satisfy their concrete row-construction equations

The partial execution's retained-row theorem is transported from each actual private
prefix to the final column state. This identifies the advice cells, the two columns
from one common lookup-sort result, and all product scans with the polynomials read
by the verifier. Product terminal rows are retained as well as usable rows.

Completion is a premise about the explicit attempt, not a conditioning of its law.
Product zero denominators are permitted in these execution equalities; the separate
constraint theorems specify where a recurrence needs a nonzero denominator.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- A present private column evaluates to the stored row at every domain point. -/
theorem privateColumnPolynomial_eval_row_of_present {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (hindex : (privateColumnIndex id).val < rows.length)
    (i : Fin 2048) :
    (privateColumnPolynomial rows id).eval (omegaOf 11 ^ i.val) =
      (rows.getD (privateColumnIndex id).val 0) i := by
  change ((rows.map (rowPolynomial (omegaOf 11))).getD (privateColumnIndex id).val 0).eval
    (omegaOf 11 ^ i.val) = _
  rw [List.getD_eq_getElem _ 0 (by simpa only [List.length_map] using hindex), List.getElem_map,
    rowPolynomial_eval (omegaOf_rows_injective 11 (by decide)), List.getD_eq_getElem rows 0 hindex]

/-- Looking up a concrete construction step by its column identity recovers its actual callback. -/
theorem plonkColumnConstructionSteps_at_index {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (id : PrivateColumnId actions)
    {hindex : (privateColumnIndex id).val < (plonkColumnConstructionSteps vk pub witness ch).length} :
    (plonkColumnConstructionSteps vk pub witness ch)[(privateColumnIndex id).val] =
      ⟨id.firstMasked, plonkConstructColumnResult vk pub witness ch id⟩ := by
  simp [plonkColumnConstructionSteps, privateColumnIndex, List.getElem_map]

/-- Every produced column preserves its computed rows, also in the prefix of a failed attempt. -/
theorem plonkColumnAttempt_retained_of_present {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (id : PrivateColumnId actions)
    (hindex : (privateColumnIndex id).val < (plonkColumnAttempt vk pub witness ch tape).columns.length) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    ∃ base, plonkConstructColumnResult vk pub witness ch id rows.reverse = some base ∧
      ∀ i : Fin 2048, i.val < id.firstMasked →
        (privateColumnPolynomial rows id).eval (omegaOf 11 ^ i.val) = base i := by
  let rows := (plonkColumnAttempt vk pub witness ch tape).columns
  obtain ⟨base, hbase, hkeep⟩ := columnAttemptFromTape_retained
    (plonkColumnConstructionSteps vk pub witness ch) []
    (tape ∘ Fin.cast (plonkColumnConstructionSteps_row_samples vk pub witness ch))
    (privateColumnIndex id).val hindex
  rw [plonkColumnConstructionSteps_at_index vk pub witness ch id] at hbase hkeep
  change plonkConstructColumnResult vk pub witness ch id
    ((rows.take (privateColumnIndex id).val).reverse ++ []) = some base at hbase
  rw [List.append_nil, plonkConstructColumnResult_prefix] at hbase
  change ∀ i : Fin 2048, i.val < id.firstMasked →
    (rows.getD (privateColumnIndex id).val 0) i = base i at hkeep
  refine ⟨base, hbase, ?_⟩
  intro i hi
  exact (privateColumnPolynomial_eval_row_of_present rows id hindex i).trans (hkeep i hi)

/-- Completion supplies the retained-row equation for every declared private column. -/
theorem plonkColumnAttempt_retained {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (id : PrivateColumnId actions) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    ∃ base, plonkConstructColumnResult vk pub witness ch id rows.reverse = some base ∧
      ∀ i : Fin 2048, i.val < id.firstMasked →
        (privateColumnPolynomial rows id).eval (omegaOf 11 ^ i.val) = base i := by
  apply plonkColumnAttempt_retained_of_present vk pub witness ch tape id
  rw [(plonkColumnAttempt_complete_iff vk pub witness ch tape).mp hcomplete]
  exact (privateColumnIndex id).isLt

/-- Usable advice cells in the completed polynomials are the supplied witness cells. -/
theorem plonkColumnAttempt_advice_rows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions) (c : Fin 10) (i : Fin 2048) (hi : i.val < 2042) :
    (privateColumnPolynomial (plonkColumnAttempt vk pub witness ch tape).columns (.advice a c)).eval
      (omegaOf 11 ^ i.val) = witness a c i := by
  obtain ⟨base, hbase, hkeep⟩ := plonkColumnAttempt_retained vk pub witness ch tape hcomplete (.advice a c)
  have hb : witness a c = base := Option.some.inj hbase
  rw [hb]
  exact hkeep i hi

/-- Both completed lookup columns come from one canonical sort of the final compressed rows. -/
theorem plonkColumnAttempt_lookup_sorted {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions) (l : Fin 3) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    ∃ b t, plonkLookupSortedRows vk pub rows ch.theta a l = some (b, t) ∧
      (∀ i < 2042, (privateColumnPolynomial rows (.lookupInput a l)).eval (omegaOf 11 ^ i) = b.getD i 0) ∧
      (∀ i < 2042, (privateColumnPolynomial rows (.lookupTable a l)).eval (omegaOf 11 ^ i) = t.getD i 0) := by
  obtain ⟨baseB, hbaseB, hkeepB⟩ := plonkColumnAttempt_retained vk pub witness ch tape hcomplete (.lookupInput a l)
  obtain ⟨baseT, hbaseT, hkeepT⟩ := plonkColumnAttempt_retained vk pub witness ch tape hcomplete (.lookupTable a l)
  simp only [plonkConstructColumnResult, List.reverse_reverse] at hbaseB hbaseT
  obtain ⟨⟨b, t⟩, hsort, hb⟩ := Option.map_eq_some_iff.mp hbaseB
  rw [hsort, Option.map_some] at hbaseT
  have ht := Option.some.inj hbaseT
  refine ⟨b, t, hsort, ?_, ?_⟩
  · intro i hi
    exact (hkeepB ⟨i, by omega⟩ hi).trans (congrFun hb ⟨i, by omega⟩).symm
  · intro i hi
    exact (hkeepT ⟨i, by omega⟩ hi).trans (congrFun ht ⟨i, by omega⟩).symm

/-- The completed lookup product agrees with the computed scan through its terminal row. -/
theorem plonkColumnAttempt_lookup_scan {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions) (l : Fin 3) (i : ℕ) (hi : i ≤ 2042) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    (privateColumnPolynomial rows (.lookupProduct a l)).eval (omegaOf 11 ^ i) =
      lookupProductRows
        (plonkLookupCompressedRows pub rows ch.theta a (vk.lookupInputExprs l))
        (plonkLookupCompressedRows pub rows ch.theta a (vk.lookupTableExprs l))
        (fun j => (privateColumnPolynomial rows (.lookupInput a l)).eval (omegaOf 11 ^ j))
        (fun j => (privateColumnPolynomial rows (.lookupTable a l)).eval (omegaOf 11 ^ j)) ch.beta ch.gamma i := by
  obtain ⟨base, hbase, hkeep⟩ := plonkColumnAttempt_retained vk pub witness ch tape hcomplete (.lookupProduct a l)
  simp only [plonkConstructColumnResult, List.reverse_reverse, Option.some.injEq] at hbase
  rw [← hbase] at hkeep
  simpa only [plonkLookupBaseRows, if_pos hi] using hkeep ⟨i, by omega⟩ (by change i < 2043; omega)

/-- Every completed permutation product uses the common factor state and inherited scan seeds. -/
theorem plonkColumnAttempt_permutation_scan {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions) (s : Fin 3) (i : ℕ) (hi : i ≤ 2042) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    (privateColumnPolynomial rows (.permutationProduct a s)).eval (omegaOf 11 ^ i) =
      permutationScanRows (plonkPermutationFactorRows pub rows a vk.permutationChunks)
        ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen 2042 s.val i := by
  obtain ⟨base, hbase, hkeep⟩ := plonkColumnAttempt_retained vk pub witness ch tape hcomplete (.permutationProduct a s)
  simp only [plonkConstructColumnResult, List.reverse_reverse, Option.some.injEq] at hbase
  rw [← hbase] at hkeep
  simpa only [plonkPermutationBaseRows, if_pos hi] using hkeep ⟨i, by omega⟩ (by change i < 2043; omega)

end Zcash.Snark.ZeroKnowledge
