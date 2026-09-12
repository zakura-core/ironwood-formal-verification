import Zcash.Snark.ZeroKnowledge.PlonkConstraints
import Zcash.Snark.ZeroKnowledge.LookupSortRows
import Zcash.Snark.ZeroKnowledge.PermutationRowConstraints

/-!
# Concrete retained-row constructors for the pinned column schedule

Lookup compression and permutation factors read the existing polynomial proof's
query layout, including rotations, from earlier masked columns in emission order.
The lookup sorter returns an explicit failure. Product rows use the proved ratio
scans through row 2042, with zero-preserving inversion and inherited chunk seeds.

These are reference computations for the supplied key and advice rows. Agreement
with the native Rust loops, including cancellation of fixed permutation cells on
zero factors, is not proved. Neither valid lookup membership nor preservation of
gate constraints under advice masking is assumed as a consequence of these definitions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Evaluate a compressed expression tuple using the actual rotated query polynomials. -/
def plonkLookupCompressedRows {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (theta : Fp) (action : Fin actions) (exprs : List (Expr Fp)) :
    ℕ → Fp :=
  let ps : ProofString (plonkProofShape actions 0) CPoly Fp := plonkPolynomialClaimProof pub rows
  fun row => compressExprs
    (fun i => (finFn ps.fixedEvals i).eval (omegaOf 11 ^ row))
    (fun i => (finFn (ps.adviceEvals action) i).eval (omegaOf 11 ^ row))
    (fun i => (finFn (ps.instanceEvals action) i).eval (omegaOf 11 ^ row)) theta exprs

/-- Lookup row compression reads exactly the feeds of the honest constraint model. -/
theorem plonkLookupCompressedRows_eq_model {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (action : Fin actions)
    (exprs : List (Expr Fp)) (row : ℕ) :
    plonkLookupCompressedRows pub rows ch.theta action exprs row =
      let model := plonkConstraintModel vk pub ch rows
      compressExprs (fun i => (model.fixedCols i).eval (omegaOf 11 ^ row))
        (fun i => (model.adviceCols action i).eval (omegaOf 11 ^ row))
        (fun i => (model.instanceCols action i).eval (omegaOf 11 ^ row)) ch.theta exprs := rfl

/-- Resolve the verifier key's packed permutation references to polynomial pairs. -/
def plonkPermutationPairPolynomials {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (action : Fin actions) (chunk : List (ColumnRef × ℕ)) :
    List (CPoly × CPoly) :=
  let ps : ProofString (plonkProofShape actions 0) CPoly Fp := plonkPolynomialClaimProof pub rows
  chunk.map fun cr =>
    (cr.1.resolve (finFn (ps.instanceEvals action)) (finFn (ps.adviceEvals action)) (finFn ps.fixedEvals),
      finFn ps.permutationCommonEvals cr.2)

/-- Evaluate the packed permutation factors at each row of each chunk. -/
def plonkPermutationFactorRows {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (action : Fin actions) (chunks : List (List (ColumnRef × ℕ))) :
    ℕ → ℕ → List (Fp × Fp) :=
  fun chunk row => (plonkPermutationPairPolynomials pub rows action (chunks.getD chunk [])).map
    (fun pair => (pair.1.eval (omegaOf 11 ^ row), pair.2.eval (omegaOf 11 ^ row)))

/-- The three-chunk constraint model uses precisely these packed polynomial pairs. -/
theorem plonkPermutationPairPolynomials_eq_model {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (action : Fin actions)
    (hchunks : vk.permutationChunks.length = 3) :
    ((plonkConstraintModel vk pub ch rows).chunks action).map Prod.snd =
      vk.permutationChunks.map (plonkPermutationPairPolynomials pub rows action) := by
  let ps : ProofString (plonkProofShape actions k) CPoly G := plonkPolynomialClaimProof pub rows
  change (((List.ofFn (ps.permutationSetEvals action)).zip vk.permutationChunks).map
    (fun sc => (sc.1, plonkPermutationPairPolynomials pub rows action sc.2))).map Prod.snd = _
  rw [List.map_map]
  change ((List.ofFn (ps.permutationSetEvals action)).zip vk.permutationChunks).map
    ((plonkPermutationPairPolynomials pub rows action) ∘ Prod.snd) = _
  rw [← List.map_map, List.map_snd_zip
    (by simpa only [List.length_ofFn, hchunks] using (Nat.le_refl 3))]

/-- Sort the compressed usable prefixes, preserving the sorter's failure result. -/
def plonkLookupSortedRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (theta : Fp) (action : Fin actions) (lookup : Fin 3) :
    Option (List Fp × List Fp) :=
  lookupSortedPrefixes 2042
    (plonkLookupCompressedRows pub rows theta action (vk.lookupInputExprs lookup))
    (plonkLookupCompressedRows pub rows theta action (vk.lookupTableExprs lookup))

/-- Membership of the actual compressed input in its table guarantees sorter success. -/
theorem plonkLookupSortedRows_exists {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (theta : Fp) (action : Fin actions) (lookup : Fin 3)
    (hmember : ∀ i < 2042, ∃ j, j < 2042 ∧
      plonkLookupCompressedRows pub rows theta action (vk.lookupInputExprs lookup) i =
        plonkLookupCompressedRows pub rows theta action (vk.lookupTableExprs lookup) j) :
    ∃ output, plonkLookupSortedRows vk pub rows theta action lookup = some output :=
  lookupSortedPrefixes_exists 2042 _ _ hmember

/-- The computed permutation column, retaining its terminal row before the suffix mask. -/
def plonkPermutationBaseRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (beta gamma : Fp) (action : Fin actions) (set : Fin 3) :
    Fin 2048 → Fp :=
  fun row => if row.val ≤ 2042 then
    permutationScanRows (plonkPermutationFactorRows pub rows action vk.permutationChunks)
      beta gamma (omegaOf 11) vk.delta vk.chunkLen 2042 set.val row.val
    else 0

/-- The lookup scan reads the actual masked input and table permutation columns. -/
def plonkLookupBaseRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (theta beta gamma : Fp) (action : Fin actions) (lookup : Fin 3) :
    Fin 2048 → Fp :=
  fun row => if row.val ≤ 2042 then
    lookupProductRows
      (plonkLookupCompressedRows pub rows theta action (vk.lookupInputExprs lookup))
      (plonkLookupCompressedRows pub rows theta action (vk.lookupTableExprs lookup))
      (fun i => (privateColumnPolynomial rows (.lookupInput action lookup)).eval (omegaOf 11 ^ i))
      (fun i => (privateColumnPolynomial rows (.lookupTable action lookup)).eval (omegaOf 11 ^ i))
      beta gamma row.val
    else 0

/-- Construct a scheduled column from the full earlier masked history, newest column first. -/
def plonkConstructColumnResult {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (id : PrivateColumnId actions) (history : ColumnHistory 2048) : Option (Fin 2048 → Fp) :=
  match id with
  | .advice a c => some (witness a c)
  | .lookupInput a l => (plonkLookupSortedRows vk pub history.reverse ch.theta a l).map
      (fun output row => output.1.getD row.val 0)
  | .lookupTable a l => (plonkLookupSortedRows vk pub history.reverse ch.theta a l).map
      (fun output row => output.2.getD row.val 0)
  | .permutationProduct a s =>
      some (plonkPermutationBaseRows vk pub history.reverse ch.beta ch.gamma a s)
  | .lookupProduct a l =>
      some (plonkLookupBaseRows vk pub history.reverse ch.theta ch.beta ch.gamma a l)

/-- Advice construction has no challenge or earlier-column dependency. -/
theorem plonkConstructColumnResult_advice {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (history : ColumnHistory 2048) (a : Fin actions) (c : Fin 10) :
    plonkConstructColumnResult vk pub witness ch (.advice a c) history = some (witness a c) := rfl

/-- Only a failed lookup sort can fail this reference column constructor. -/
theorem plonkConstructColumnResult_eq_none {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (history : ColumnHistory 2048) (id : PrivateColumnId actions) :
    plonkConstructColumnResult vk pub witness ch id history = none ↔
      match id with
      | .lookupInput a l | .lookupTable a l =>
        plonkLookupSortedRows vk pub history.reverse ch.theta a l = none
      | _ => False := by
  cases id <;> simp [plonkConstructColumnResult]

/-- Every retained-row constructor is independent of challenges after `theta`, `beta`, `gamma`. -/
theorem plonkConstructColumnResult_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (hbeta : ch.beta = ch'.beta) (hgamma : ch.gamma = ch'.gamma) :
    plonkConstructColumnResult vk pub witness ch = plonkConstructColumnResult vk pub witness ch' := by
  funext id history
  cases id <;> simp only [plonkConstructColumnResult, htheta, hbeta, hgamma]

/-- Lookup permutation construction uses only `theta`, before the product challenges arrive. -/
theorem plonkConstructColumnResult_lookup_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (history : ColumnHistory 2048) (a : Fin actions) (l : Fin 3) :
    plonkConstructColumnResult vk pub witness ch (.lookupInput a l) history =
      plonkConstructColumnResult vk pub witness ch' (.lookupInput a l) history ∧
    plonkConstructColumnResult vk pub witness ch (.lookupTable a l) history =
      plonkConstructColumnResult vk pub witness ch' (.lookupTable a l) history := by
  simp only [plonkConstructColumnResult, htheta, and_self]

end Zcash.Snark.ZeroKnowledge
