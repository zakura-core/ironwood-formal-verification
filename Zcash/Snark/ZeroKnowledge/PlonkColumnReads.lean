import Zcash.Snark.ZeroKnowledge.PlonkColumnOrder
import Zcash.Snark.ZeroKnowledge.PlonkRowConstruction

/-!
# Construction-time queries agree with the completed column state

The proof layout reads private columns by their emission positions. Truncating after
a column's position preserves its entire polynomial, hence every rotated query.
The phase bounds ensure that lookup and product construction read only preceding
columns. Both computations of a lookup sort and every inherited product seed can
therefore be compared using one final row state.

These equalities hold for arbitrary row lists, including lists with missing columns
handled by the existing zero defaults. They do not assume correctness of a witness,
successful sorting, or nonzero product denominators.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Truncation preserves reads before its cutoff, allowing column histories to be replaced by their
available prefixes. -/
private theorem getD_take_of_lt {A : Type*} (values : List A) (cut i : ℕ) (fallback : A)
    (hi : i < cut) : (values.take cut).getD i fallback = values.getD i fallback := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- A prefix containing a column's position preserves the entire column polynomial. -/
theorem privateColumnPolynomial_take {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (cut : ℕ) (hindex : (privateColumnIndex id).val < cut) :
    privateColumnPolynomial (rows.take cut) id = privateColumnPolynomial rows id := by
  unfold privateColumnPolynomial
  rw [List.map_take]
  exact getD_take_of_lt _ cut _ 0 hindex

/-- Every rotated query is also unchanged by dropping columns after its position. -/
theorem plonkRotatedColumn_take {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (cut : ℕ) (hindex : (privateColumnIndex id).val < cut)
    (i : Fin 4) :
    plonkRotatedColumn (rows.take cut) id i = plonkRotatedColumn rows id i := by
  rw [plonkRotatedColumn, privateColumnPolynomial_take rows id cut hindex]
  rfl

/-- Once all advice columns have been emitted, the proof's whole advice query vector is fixed. -/
theorem plonkPolynomialClaimProof_advice_take {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (cut : ℕ) (hcut : 10 * actions ≤ cut) (a : Fin actions) :
    (plonkPolynomialClaimProof (k := k) (G := G) pub (rows.take cut)).adviceEvals a =
      (plonkPolynomialClaimProof (k := k) (G := G) pub rows).adviceEvals a := by
  funext j
  exact plonkRotatedColumn_take rows (.advice a (plonkAdviceQueryOrder j).1) cut
    (lt_of_lt_of_le (privateColumnIndex_bounds (.advice a (plonkAdviceQueryOrder j).1)) hcut)
    ((plonkAdviceQueryOrder j).2.castLE (by decide))

/-- Lookup compression reads no private columns beyond the advice phase. -/
theorem plonkLookupCompressedRows_take {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 10 * actions ≤ cut)
    (theta : Fp) (a : Fin actions) (exprs : List (Expr Fp)) :
    plonkLookupCompressedRows pub (rows.take cut) theta a exprs =
      plonkLookupCompressedRows pub rows theta a exprs := by
  simp only [plonkLookupCompressedRows, plonkPolynomialClaimProof_advice_take pub rows cut hcut]
  rfl

/-- Packed permutation references likewise read only advice and public polynomials. -/
theorem plonkPermutationPairPolynomials_take {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 10 * actions ≤ cut)
    (a : Fin actions) (chunk : List (ColumnRef × ℕ)) :
    plonkPermutationPairPolynomials pub (rows.take cut) a chunk =
      plonkPermutationPairPolynomials pub rows a chunk := by
  simp only [plonkPermutationPairPolynomials, plonkPolynomialClaimProof_advice_take pub rows cut hcut]
  rfl

/-- Every permutation factor row agrees between an adequate prefix and the final state. -/
theorem plonkPermutationFactorRows_take {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 10 * actions ≤ cut)
    (a : Fin actions) (chunks : List (List (ColumnRef × ℕ))) :
    plonkPermutationFactorRows pub (rows.take cut) a chunks =
      plonkPermutationFactorRows pub rows a chunks := by
  funext chunk row
  simp only [plonkPermutationFactorRows, plonkPermutationPairPolynomials_take pub rows cut hcut]

/-- Both lookup permutation columns use the same complete sorting result, including failure. -/
theorem plonkLookupSortedRows_take {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 10 * actions ≤ cut)
    (theta : Fp) (a : Fin actions) (l : Fin 3) :
    plonkLookupSortedRows vk pub (rows.take cut) theta a l =
      plonkLookupSortedRows vk pub rows theta a l := by
  simp only [plonkLookupSortedRows, plonkLookupCompressedRows_take pub rows cut hcut]

/-- Recomputed permutation seeds and scans use the same factors at every product step. -/
theorem plonkPermutationBaseRows_take {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 10 * actions ≤ cut)
    (beta gamma : Fp) (a : Fin actions) (s : Fin 3) :
    plonkPermutationBaseRows vk pub (rows.take cut) beta gamma a s =
      plonkPermutationBaseRows vk pub rows beta gamma a s := by
  funext row
  simp only [plonkPermutationBaseRows, plonkPermutationFactorRows_take pub rows cut hcut]

/-- Lookup scans read only advice and the already constructed lookup permutation columns. -/
theorem plonkLookupBaseRows_take {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (cut : ℕ) (hcut : 16 * actions ≤ cut)
    (theta beta gamma : Fp) (a : Fin actions) (l : Fin 3) :
    plonkLookupBaseRows vk pub (rows.take cut) theta beta gamma a l =
      plonkLookupBaseRows vk pub rows theta beta gamma a l := by
  have hadvice : 10 * actions ≤ cut := by omega
  have hb := lt_of_lt_of_le (privateColumnIndex_bounds (.lookupInput a l)).2 hcut
  have ht := lt_of_lt_of_le (privateColumnIndex_bounds (.lookupTable a l)).2 hcut
  funext row
  simp only [plonkLookupBaseRows, plonkLookupCompressedRows_take pub rows cut hadvice,
    privateColumnPolynomial_take rows (.lookupInput a l) cut hb,
    privateColumnPolynomial_take rows (.lookupTable a l) cut ht]

/-- Every scheduled construction gives the same result from its actual prefix as from all columns. -/
theorem plonkConstructColumnResult_prefix {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (rows : ColumnHistory 2048) (id : PrivateColumnId actions) :
    plonkConstructColumnResult vk pub witness ch id ((rows.take (privateColumnIndex id).val).reverse) =
      plonkConstructColumnResult vk pub witness ch id rows.reverse := by
  cases id with
  | advice a c => rfl
  | lookupInput a l =>
    simp only [plonkConstructColumnResult, List.reverse_reverse,
      plonkLookupSortedRows_take vk pub rows _ (privateColumnIndex_bounds (.lookupInput a l)).1]
  | lookupTable a l =>
    simp only [plonkConstructColumnResult, List.reverse_reverse,
      plonkLookupSortedRows_take vk pub rows _ (privateColumnIndex_bounds (.lookupTable a l)).1]
  | permutationProduct a s =>
    have hcut : 10 * actions ≤ (privateColumnIndex (.permutationProduct a s)).val := by
      have h := (privateColumnIndex_bounds (.permutationProduct a s)).1
      omega
    simp only [plonkConstructColumnResult, List.reverse_reverse,
      plonkPermutationBaseRows_take vk pub rows _ hcut]
  | lookupProduct a l =>
    have hcut : 16 * actions ≤ (privateColumnIndex (.lookupProduct a l)).val := by
      have h := (privateColumnIndex_bounds (.lookupProduct a l)).1
      omega
    simp only [plonkConstructColumnResult, List.reverse_reverse,
      plonkLookupBaseRows_take vk pub rows _ hcut]

end Zcash.Snark.ZeroKnowledge
