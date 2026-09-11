import Zcash.Snark.Fixtures.Prover.Scan
import Zcash.Snark.ZeroKnowledge.PlonkSampling
import Zcash.Snark.ZeroKnowledge.PlonkColumnRecipesCost
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceResult

/-!
# Replaying the private material on the captured tape

The existing batch decoder supplies the suffix masks, linear mask, and commitment
blinds in their original order. Cached row constructors feed that same decoder
and sequential history. The result equals the reference prover's full private
state on every supplied tape.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- Run the original lookup sorter with direct row readers. -/
def sortedRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (theta : Fp) (a : Fin actions) (l : Fin 3) :
    Option (List Fp × List Fp) :=
  lookupSortedPrefixes 2042 (lookupValues instances fixed rows theta a (vk.lookupInputExprs l))
    (lookupValues instances fixed rows theta a (vk.lookupTableExprs l))

/-- Direct reads retain the sorter's exact success or failure and ordered output. -/
theorem sortedRows_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (rows : ColumnHistory 2048)
    (theta : Fp) (a : Fin actions) (l : Fin 3) :
    sortedRows vk instances fixed rows theta a l =
      plonkLookupSortedRows vk (plonkPublicPolynomialsFromRows instances fixed sigma) rows theta a l := by
  unfold sortedRows plonkLookupSortedRows
  congr 1 <;> funext row <;> exact lookupValues_result instances fixed sigma rows theta a _ row

/-- Construct and cache each scheduled column from the complete earlier masked history. -/
def constructColumn {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (id : PrivateColumnId actions) (history : ColumnHistory 2048) :
    Option (Vector Fp 2048) :=
  match id with
  | .advice a c => some (cacheFn (witness a c))
  | .lookupInput a l => (sortedRows vk instances fixed history.reverse ch.theta a l).map
      (fun output => cacheFn (fun row => output.1.getD row.val 0))
  | .lookupTable a l => (sortedRows vk instances fixed history.reverse ch.theta a l).map
      (fun output => cacheFn (fun row => output.2.getD row.val 0))
  | .permutationProduct a s =>
      some (permutationColumn vk instances fixed sigma history.reverse ch.beta ch.gamma a s)
  | .lookupProduct a l =>
      some (lookupColumn vk instances fixed history.reverse ch.theta ch.beta ch.gamma a l)

/-- Every cached constructor agrees with the reference, including lookup failure. -/
theorem constructColumn_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (id : PrivateColumnId actions) (history : ColumnHistory 2048) :
    (constructColumn vk instances fixed sigma witness ch id history).map Vector.get =
      plonkConstructColumnResult vk (plonkPublicPolynomialsFromRows instances fixed sigma)
        witness ch id history := by
  cases id <;> simp only [constructColumn, plonkConstructColumnResult, Option.map_map,
    Option.map_some, Function.comp_def, cacheFn_result, sortedRows_result vk instances fixed sigma,
    permutationColumn_result, lookupColumn_result vk instances fixed sigma]

/-- Store each history column before installing its constant-time row reader. -/
def cachedHistory (history : List (List Fp)) : ColumnHistory 2048 :=
  let arrays := history.map List.toArray
  arrays.map (fun values row => values[row.val]?.getD 0)

/-- Array storage preserves the reference history's default and every supplied value. -/
theorem cachedHistory_result (history : List (List Fp)) :
    cachedHistory history = storedColumnHistory 2048 history := by
  simp only [cachedHistory, storedColumnHistory, List.map_map, Function.comp_def,
    List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- Totalize a failed column constructor with the original all-zero row. -/
def rowsOrZero (rows : Option (Vector Fp 2048)) : Vector Fp 2048 :=
  rows.getD (cacheFn (fun _ => 0))

/-- Totalization preserves the reference's failure fallback without recomputing stored columns. -/
theorem rowsOrZero_result (rows : Option (Vector Fp 2048)) :
    (rowsOrZero rows).get = (rows.map Vector.get).getD 0 := by
  cases rows with
  | none => exact cacheFn_result _
  | some rows => rfl

/-- Complete one constructor before materializing its rows for the sequential sampler. -/
def constructStored {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (id : PrivateColumnId actions) (history : List (List Fp)) :
    List Fp × ℕ :=
  let base := constructColumn vk instances fixed sigma witness ch id (cachedHistory history)
  (List.ofFn (rowsOrZero base).get, 0)

/-- Stored construction retains the reference's explicit zero-column fallback for failed lookups. -/
theorem constructStored_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (id : PrivateColumnId actions) (history : List (List Fp)) :
    (constructStored vk instances fixed sigma witness ch id history).1 =
      List.ofFn (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows instances fixed sigma) witness ch id
        (storedColumnHistory 2048 history)) := by
  simp only [constructStored, rowsOrZero_result, constructColumn_result, cachedHistory_result]
  rfl

/-- Run the existing stored sequential sampler, retaining every earlier masked column. -/
def constructedRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (tape : ℕ → Fp) : ColumnHistory 2048 :=
  cachedHistory (storedColumnRowsFromTapeCosted 2048 0
    (constructStored vk instances fixed sigma witness ch) (privateColumnRecipesCosted actions).1 []
    (fun index => (tape index, 0)) 0).1

/-- Storage changes neither the column schedule nor any row-mask offset. -/
theorem constructedRows_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (tape : ℕ → Fp) :
    constructedRows vk instances fixed sigma witness ch tape =
      columnRowsFromTape (plonkColumnSteps (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows instances fixed sigma) witness ch)) []
        (fun index => tape index.val) := by
  unfold constructedRows
  rw [cachedHistory_result, storedColumnRowsFromTapeCosted_result _ _ _ _
    (constructStored_result vk instances fixed sigma witness ch), privateColumnRecipesCosted_steps]
  simp only [Nat.zero_add]
  exact storedColumnHistory_materialize _

/-- Reindex the fixed-size pre-IPA tape without changing any sample. -/
def materialTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (148 * actions + 12) → Fp) :
    Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp :=
  fun i => tape ⟨i.val, by simpa only [plonkColumnBatches_sample_count] using i.isLt⟩

/-- Run the original batched sampler and retain its complete private state. -/
def material {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (tape : Fin (148 * actions + 12) → Fp) : PlonkPrivateMaterial actions :=
  let construct := plonkTotalColumnConstructor vk
    (plonkPublicPolynomialsFromRows instances fixed sigma) witness ch
  let coins := plonkPreIpaCoinsEquiv construct (materialTape construct tape)
  let rowTape := Array.ofFn coins.1
  (constructedRows vk instances fixed sigma witness ch (fun i => rowTape[i]?.getD 0), coins.2)

/-- The replay's private state is exactly the reference state on the identical batched tape. -/
theorem material_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges k Fp) (tape : Fin (148 * actions + 12) → Fp) :
    material vk instances fixed sigma witness ch tape =
      let construct := plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows instances fixed sigma) witness ch
      plonkMaterialFromTape construct [] (materialTape construct tape) := by
  simp only [material, constructedRows_result, plonkMaterialFromTape]
  congr 2
  funext index
  simp only [Array.getElem?_ofFn, index.isLt, dite_true, Option.getD_some]

end Zcash.Snark.Fixtures.Prover
