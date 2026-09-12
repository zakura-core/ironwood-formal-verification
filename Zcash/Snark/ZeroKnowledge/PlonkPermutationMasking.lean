import Zcash.Snark.ZeroKnowledge.PlonkAdviceRows
import Zcash.Snark.ZeroKnowledge.PlonkLookupRows

/-!
# Masking preserves the usable permutation factors

The first ten advice queries are exactly the ten unrotated columns. A public key
whose permutation references use only those advice queries therefore reads original
witness cells on every usable row. Fixed and instance values are public and unchanged.
The statement covers every tape, including executions with a later failed lookup sort.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- The first ten query positions are the unrotated advice columns in column order. -/
theorem plonkAdviceQueryOrder_current (c : Fin 10) :
    plonkAdviceQueryOrder (c.castLE (by decide)) = (c, 0) := by
  fin_cases c <;> rfl

/-- The proof's current-row advice query is the corresponding private column polynomial. -/
theorem plonkPolynomialClaimProof_advice_current {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (a : Fin actions) (c : Fin 10) :
    (plonkPolynomialClaimProof (k := k) (G := G) pub rows).adviceEvals a
        (c.castLE (by change 10 ≤ 25; decide)) =
      privateColumnPolynomial rows (.advice a c) := by
  change plonkRotatedColumn rows (.advice a (plonkAdviceQueryOrder (c.castLE (by decide))).1)
    ((plonkAdviceQueryOrder (c.castLE (by decide))).2.castLE (by decide)) = _
  rw [plonkAdviceQueryOrder_current]
  exact plonkRotatedColumn_zero rows (.advice a c)

/-- A permutation reference either reads public data or one of the unrotated advice queries. -/
def plonkPermutationRefUnrotated : ColumnRef → Bool
  | .advice q => decide (q < 10)
  | .fixed _ | .instance _ => true

/-- Check the public permutation query layout without inspecting a private witness. -/
def plonkPermutationQueriesUnrotated (chunks : List (List (ColumnRef × ℕ))) : Bool :=
  chunks.flatten.all fun entry => plonkPermutationRefUnrotated entry.1

/-- An unrotated permutation reference has the same evaluation when advice evaluations agree,
transporting masking agreement to copy-product inputs. -/
private theorem permutationRef_eval_congr {actions : ℕ}
    (pub : PlonkPublicPolynomials actions) (left right : ColumnHistory 2048)
    (a : Fin actions) (x : Fp)
    (hadvice : ∀ c : Fin 10, (privateColumnPolynomial left (.advice a c)).eval x =
      (privateColumnPolynomial right (.advice a c)).eval x)
    (ref : ColumnRef) (href : plonkPermutationRefUnrotated ref = true) :
    let masked : ProofString (plonkProofShape actions 0) CPoly Fp :=
      plonkPolynomialClaimProof pub left
    let original : ProofString (plonkProofShape actions 0) CPoly Fp :=
      plonkPolynomialClaimProof pub right
    (ref.resolve (finFn (masked.instanceEvals a)) (finFn (masked.adviceEvals a)) (finFn masked.fixedEvals)).eval x =
      (ref.resolve (finFn (original.instanceEvals a)) (finFn (original.adviceEvals a))
        (finFn original.fixedEvals)).eval x := by
  cases ref with
  | fixed q => rfl
  | «instance» q => rfl
  | advice q =>
    have hq : q < 10 := of_decide_eq_true href
    have hq25 : q < (plonkProofShape actions 0).numAdviceQueries := by
      change q < 25
      exact lt_trans hq (by decide)
    change (finFn ((plonkPolynomialClaimProof (k := 0) (G := Fp) pub left).adviceEvals a) q).eval x =
      (finFn ((plonkPolynomialClaimProof (k := 0) (G := Fp) pub right).adviceEvals a) q).eval x
    simp only [finFn, dif_pos hq25]
    exact (congrArg (fun poly : CPoly => poly.eval x)
      (plonkPolynomialClaimProof_advice_current (k := 0) (G := Fp) pub left a ⟨q, hq⟩)).trans
        ((hadvice ⟨q, hq⟩).trans (congrArg (fun poly : CPoly => poly.eval x)
          (plonkPolynomialClaimProof_advice_current (k := 0) (G := Fp) pub right a ⟨q, hq⟩)).symm)

/-- Every supported permutation query reads the same usable value before and after masking. -/
theorem plonkPermutationRef_usable {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) (i : Fin 2048) (hi : i.val < 2042)
    (ref : ColumnRef) (href : plonkPermutationRefUnrotated ref = true) :
    let masked : ProofString (plonkProofShape actions 0) CPoly Fp :=
      plonkPolynomialClaimProof pub (plonkTotalColumnRows vk pub witness ch tape)
    let original : ProofString (plonkProofShape actions 0) CPoly Fp :=
      plonkPolynomialClaimProof pub (plonkUnmaskedAdviceRows witness)
    (ref.resolve (finFn (masked.instanceEvals a)) (finFn (masked.adviceEvals a)) (finFn masked.fixedEvals)).eval
        (omegaOf 11 ^ i.val) =
      (ref.resolve (finFn (original.instanceEvals a)) (finFn (original.adviceEvals a))
        (finFn original.fixedEvals)).eval (omegaOf 11 ^ i.val) := by
  apply permutationRef_eval_congr pub _ _ a _ _ ref href
  intro c
  rw [plonkTotalColumnRows_advice_rows vk pub witness ch tape a c i hi, plonkUnmaskedAdviceRows_eval]

/-- Packed factor counts depend only on the key's chunk layout. -/
theorem plonkPermutationFactorRows_length {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ))) (c i : ℕ) :
    (plonkPermutationFactorRows pub rows a chunks c i).length = (chunks.getD c []).length := by
  simp only [plonkPermutationFactorRows, plonkPermutationPairPolynomials, List.length_map]

/-- Equal current-row advice values give the same public-layout permutation factor list. -/
theorem plonkPermutationFactorRows_congr {actions : ℕ}
    (pub : PlonkPublicPolynomials actions) (left right : ColumnHistory 2048)
    (chunks : List (List (ColumnRef × ℕ)))
    (hqueries : plonkPermutationQueriesUnrotated chunks = true)
    (a : Fin actions) (c i : ℕ)
    (hadvice : ∀ col : Fin 10, (privateColumnPolynomial left (.advice a col)).eval (omegaOf 11 ^ i) =
      (privateColumnPolynomial right (.advice a col)).eval (omegaOf 11 ^ i)) :
    plonkPermutationFactorRows pub left a chunks c i = plonkPermutationFactorRows pub right a chunks c i := by
  by_cases hc : c < chunks.length
  · simp only [plonkPermutationFactorRows, plonkPermutationPairPolynomials, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro entry hentry
    have hmem : entry ∈ chunks.flatten := by
      apply List.mem_flatten.mpr
      refine ⟨chunks.getD c [], ?_, hentry⟩
      rw [List.getD_eq_getElem _ _ hc]
      exact List.getElem_mem hc
    have href := (List.all_eq_true.mp hqueries) entry hmem
    exact Prod.ext (permutationRef_eval_congr pub left right a _ hadvice entry.1 href) rfl
  · simp only [plonkPermutationFactorRows, List.getD_eq_default _ _ (Nat.le_of_not_gt hc),
      plonkPermutationPairPolynomials, List.map_nil]

/-- The full usable-row factor lists are unchanged by all private masks and later challenges. -/
theorem plonkPermutationFactorRows_masked {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (a : Fin actions) (c : ℕ) (i : Fin 2048) (hi : i.val < 2042) :
    plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks c i.val =
      plonkPermutationFactorRows pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks c i.val := by
  apply plonkPermutationFactorRows_congr pub _ _ vk.permutationChunks hqueries a c i.val
  intro col
  rw [plonkTotalColumnRows_advice_rows vk pub witness ch tape a col i hi, plonkUnmaskedAdviceRows_eval]

end Zcash.Snark.ZeroKnowledge
