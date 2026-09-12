import Zcash.Snark.ZeroKnowledge.ColumnCompletion
import Zcash.Snark.ZeroKnowledge.PlonkOriginalRows

/-!
# Original lookup validity makes the concrete column attempt complete

Lookup sorts are the only failing retained-row constructors. Once their compressed
memberships hold in the total final advice state, the prefix-read theorem gives the
same successful sorts at their actual scheduled positions. The partial runner thus
completes on every tape. Product denominators can still be zero; this theorem concerns
construction completion, not acceptance of the full proof.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The first occurrence of an indexed list element appears no later than that index, supporting
lookup completion with repeated values. -/
private theorem idxOf_getElem_le {A : Type*} [DecidableEq A]
    (values : List A) (i : ℕ) (hi : i < values.length) : values.idxOf values[i] ≤ i := by
  have htake : i < (values.take (i + 1)).length := by simp; omega
  have hmem : values[i] ∈ values.take (i + 1) := by
    simpa only [List.getElem_take] using List.getElem_mem htake
  exact Nat.le_of_lt_succ ((List.mem_take_iff_idxOf_lt (List.getElem_mem hi)).mp hmem)

/-- Every scheduled prefix constructor succeeds if the final advice state has successful sorts. -/
theorem plonkConstructColumnResult_ne_none_of_sorted {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (rows : ColumnHistory 2048)
    (hsorts : ∀ a : Fin actions, ∀ lookup : Fin 3, plonkLookupSortedRows vk pub rows ch.theta a lookup ≠ none)
    (id : PrivateColumnId actions) (cut : ℕ) (hcut : (privateColumnIndex id).val ≤ cut) :
    plonkConstructColumnResult vk pub witness ch id (rows.take cut).reverse ≠ none := by
  cases id with
  | advice a c => simp [plonkConstructColumnResult]
  | permutationProduct a s => simp [plonkConstructColumnResult]
  | lookupProduct a l => simp [plonkConstructColumnResult]
  | lookupInput a l =>
      have hadvice : 10 * actions ≤ cut := (privateColumnIndex_bounds (.lookupInput a l)).1.trans hcut
      intro hnone
      have hfailed := (plonkConstructColumnResult_eq_none vk pub witness ch (rows.take cut).reverse (.lookupInput a l)).mp hnone
      change plonkLookupSortedRows vk pub (rows.take cut).reverse.reverse ch.theta a l = none at hfailed
      rw [List.reverse_reverse, plonkLookupSortedRows_take vk pub rows cut hadvice] at hfailed
      exact hsorts a l hfailed
  | lookupTable a l =>
      have hadvice : 10 * actions ≤ cut := (privateColumnIndex_bounds (.lookupTable a l)).1.trans hcut
      intro hnone
      have hfailed := (plonkConstructColumnResult_eq_none vk pub witness ch (rows.take cut).reverse (.lookupTable a l)).mp hnone
      change plonkLookupSortedRows vk pub (rows.take cut).reverse.reverse ch.theta a l = none at hfailed
      rw [List.reverse_reverse, plonkLookupSortedRows_take vk pub rows cut hadvice] at hfailed
      exact hsorts a l hfailed

/-- Successful sorts in the total state imply completion of the actual partial schedule on the same tape. -/
theorem plonkColumnAttempt_complete_of_sorted {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hsorts : ∀ a : Fin actions, ∀ lookup : Fin 3,
      plonkLookupSortedRows vk pub (plonkTotalColumnRows vk pub witness ch tape) ch.theta a lookup ≠ none) :
    (plonkColumnAttempt vk pub witness ch tape).complete = true := by
  apply columnAttemptFromTape_complete_of_total
  intro j hj
  have hjOrder : j < (privateColumnOrder actions).length := by
    simpa only [plonkColumnConstructionSteps, List.length_map] using hj
  let id := (privateColumnOrder actions)[j]
  have hindex : (privateColumnIndex id).val ≤ j := idxOf_getElem_le (privateColumnOrder actions) j hjOrder
  have hstep : (plonkColumnConstructionSteps vk pub witness ch)[j] =
      (⟨id.firstMasked, plonkConstructColumnResult vk pub witness ch id⟩ : ColumnAttemptStep 2048) := by
    simp only [plonkColumnConstructionSteps, List.getElem_map]
    rfl
  have hrows := columnRowsFromTape_cast_eq (plonkColumnConstructionSteps_totalize vk pub witness ch)
    (plonkColumnConstructionSteps_row_samples vk pub witness ch)
    (plonkColumnSteps_row_samples (plonkTotalColumnConstructor vk pub witness ch)) [] tape
  change _ = plonkTotalColumnRows vk pub witness ch tape at hrows
  rw [hstep]
  change plonkConstructColumnResult vk pub witness ch id
    (((columnRowsFromTape ((plonkColumnConstructionSteps vk pub witness ch).map ColumnAttemptStep.totalize) []
      (tape ∘ Fin.cast (plonkColumnConstructionSteps_row_samples vk pub witness ch))).take j).reverse ++ []) ≠ none
  rw [hrows, List.append_nil]
  exact plonkConstructColumnResult_ne_none_of_sorted vk pub witness ch _ hsorts id j hindex

/-- Original lookup tuple validity and the public mask profile make construction complete on every tape. -/
theorem plonkColumnAttempt_complete_of_original {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (ch : Challenges k Fp) (tape : Fin (126 * actions) → Fp) :
    (plonkColumnAttempt vk pub witness ch tape).complete = true := by
  apply plonkColumnAttempt_complete_of_sorted vk pub witness ch tape
  intro a lookup
  obtain ⟨output, houtput⟩ := plonkLookupSortedRows_exists vk pub _ ch.theta a lookup
    (plonkTotalColumnRows_lookupMembership vk pub witness profile hvalid ch tape a lookup)
  rw [houtput]
  exact Option.some_ne_none output

end Zcash.Snark.ZeroKnowledge
