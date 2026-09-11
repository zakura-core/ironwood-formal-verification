import Zcash.Snark.Fixtures.Prover.RowFeeds

/-!
# Storing product-scan prefixes

The replay computes each exclusive running-product prefix once. Total field
inversion is retained, including at zero, so these adapters preserve the
reference algorithm on exceptional denominators as well.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- Materialize every exclusive ratio-scan state from row zero through the terminal row. -/
def scan (num den : ℕ → Fp) (initial : Fp) (count : ℕ) : Vector Fp (count + 1) :=
  let values := ((List.range count).scanl (fun acc i => acc * num i / den i) initial).toArray
  ⟨values, by simp only [values, List.size_toArray, List.length_scanl, List.length_range]⟩

/-- Folding a natural prefix is the recursive ratio scan used by the reference prover. -/
private theorem scan_fold (num den : ℕ → Fp) (initial : Fp) (count : ℕ) :
    (List.range count).foldl (fun acc i => acc * num i / den i) initial =
      runningProductRows num den initial count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rfl

/-- Every stored prefix equals the corresponding recursive reference state. -/
theorem scan_result (num den : ℕ → Fp) (initial : Fp) (count : ℕ) (i : Fin (count + 1)) :
    (scan num den initial count).get i = runningProductRows num den initial i.val := by
  simp only [scan, Vector.get, List.getElem_toArray, List.getElem_scanl, List.take_range, Fin.val_cast]
  rw [Nat.min_eq_left (by omega : i.val ≤ count), scan_fold]

/-- Chain complete scans using the actual terminal value of every preceding chunk. -/
def scanInitial (num den : ℕ → ℕ → Fp) (count : ℕ) : ℕ → Fp
  | 0 => 1
  | chunk + 1 => (scan (num chunk) (den chunk) (scanInitial num den count chunk) count).get ⟨count, by omega⟩

/-- Cached chunk boundaries equal the reference prover's inherited seeds. -/
theorem scanInitial_result (num den : ℕ → ℕ → Fp) (count chunk : ℕ) :
    scanInitial num den count chunk = chainedProductInitial num den count chunk := by
  induction chunk with
  | zero => rfl
  | succ chunk ih => rw [scanInitial, scan_result, ih]; rfl

/-- Materialize a permutation chunk while leaving its masked suffix to the tape sampler. -/
def permutationColumn {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (rows : ColumnHistory 2048)
    (beta gamma : Fp) (a : Fin actions) (s : Fin 3) : Vector Fp 2048 :=
  let pairs := permutationPairs instances fixed sigma rows a vk.permutationChunks
  let num := permutationRowNumerator pairs beta gamma (omegaOf 11) vk.delta vk.chunkLen
  let den := permutationRowDenominator pairs beta gamma
  let values := scan (num s.val) (den s.val) (scanInitial num den 2042 s.val) 2042
  cacheFn (fun row => if h : row.val ≤ 2042 then values.get ⟨row.val, by omega⟩ else 0)

/-- The cached permutation column preserves every reference row and its inherited chunk seed. -/
theorem permutationColumn_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (rows : ColumnHistory 2048)
    (beta gamma : Fp) (a : Fin actions) (s : Fin 3) :
    (permutationColumn vk instances fixed sigma rows beta gamma a s).get =
      plonkPermutationBaseRows vk (plonkPublicPolynomialsFromRows instances fixed sigma)
        rows beta gamma a s := by
  have hp : permutationPairs instances fixed sigma rows a vk.permutationChunks =
      plonkPermutationFactorRows (plonkPublicPolynomialsFromRows instances fixed sigma)
        rows a vk.permutationChunks :=
    funext fun chunk => funext (permutationPairs_result instances fixed sigma rows a vk.permutationChunks chunk)
  funext row
  simp only [permutationColumn, cacheFn_result, hp, plonkPermutationBaseRows]
  split_ifs <;> simp only [scan_result, scanInitial_result]
  rfl

/-- Materialize the lookup scan from compressed inputs and the earlier masked sorted columns. -/
def lookupColumn {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (theta beta gamma : Fp) (a : Fin actions) (l : Fin 3) : Vector Fp 2048 :=
  let input := lookupValues instances fixed rows theta a (vk.lookupInputExprs l)
  let table := lookupValues instances fixed rows theta a (vk.lookupTableExprs l)
  let values := scan
    (fun i => (input i + beta) * (table i + gamma))
    (fun i => (privateRow rows (.lookupInput a l) (domainRow i) + beta) *
      (privateRow rows (.lookupTable a l) (domainRow i) + gamma)) 1 2042
  cacheFn (fun row => if h : row.val ≤ 2042 then values.get ⟨row.val, by omega⟩ else 0)

/-- The cached lookup column is the complete reference scan, with total inversion unchanged. -/
theorem lookupColumn_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (rows : ColumnHistory 2048)
    (theta beta gamma : Fp) (a : Fin actions) (l : Fin 3) :
    (lookupColumn vk instances fixed rows theta beta gamma a l).get =
      plonkLookupBaseRows vk (plonkPublicPolynomialsFromRows instances fixed sigma)
        rows theta beta gamma a l := by
  funext row
  simp only [lookupColumn, cacheFn_result, lookupValues_result instances fixed sigma, privateRow_result,
    ← domainRow_point, plonkLookupBaseRows]
  split_ifs <;> simp only [scan_result]
  rfl

end Zcash.Snark.Fixtures.Prover
