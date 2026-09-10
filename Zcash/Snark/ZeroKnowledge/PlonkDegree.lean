import Zcash.Snark.ZeroKnowledge.PlonkConstraints
import Zcash.Snark.ZeroKnowledge.LookupDegree

/-!
# Capacity of the computed PLONK quotient

The row polynomials have degree at most 2047. The public circuit profile bounds gates
by nine column factors, permutation chunks by seven columns, lookup inputs by four
factors, and lookup tables by one. Consequently the combined numerator has degree at
most `9 * 2047`, strictly below the capacity required for eight quotient pieces.
The bound holds for every row state, without a witness-correctness assumption.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial

/-- A syntactic circuit profile sufficient for the pinned eight-piece quotient. -/
structure PlonkDegreeProfile {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) : Prop where
  gates : ∀ e ∈ vk.gates, e.degreeBound ≤ 9
  chunks : ∀ chunk ∈ vk.permutationChunks, chunk.length ≤ 7
  inputs : ∀ l e, e ∈ vk.lookupInputExprs l → e.degreeBound ≤ 4
  tables : ∀ l e, e ∈ vk.lookupTableExprs l → e.degreeBound ≤ 1

/-- A rotation does not increase a row polynomial's degree. -/
theorem plonkRotatedColumn_natDegree_le {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (i : Fin 4) :
    (plonkRotatedColumn rows id i).natDegree ≤ 2047 := by
  rw [plonkRotatedColumn, natDegree_comp]
  have hfactor : (C (plonkQueryFactors i) * X : CPoly).natDegree ≤ 1 :=
    le_trans (natDegree_C_mul_le _ _) natDegree_X_le
  calc
    _ ≤ (privateColumnPolynomial rows id).natDegree * 1 := Nat.mul_le_mul_left _ hfactor
    _ ≤ 2047 := by simpa only [Nat.mul_one] using
      (Nat.le_of_lt_succ (privateColumnPolynomial_natDegree_lt rows id))

/-- Each canonical selector is itself a row polynomial. -/
theorem canonicalLagrangePolynomials_natDegree_lt {n blinding : ℕ} (omega : Fp)
    (hblinding : blinding < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val) :
    let selectors := canonicalLagrangePolynomials omega hblinding
    selectors.1.natDegree < n ∧ selectors.2.1.natDegree < n ∧ selectors.2.2.natDegree < n := by
  have hdegree (values : Fin n → Fp) : (rowPolynomial omega values).natDegree < n :=
    rowPolynomial_natDegree_lt hrows (Nat.zero_lt_of_lt hblinding)
  exact ⟨hdegree _, hdegree _, hdegree _⟩

/-- The fixed selector triple satisfies the same bound as every private row polynomial. -/
theorem plonkSelectors_natDegree_le :
    plonkSelectors.1.natDegree ≤ 2047 ∧ plonkSelectors.2.1.natDegree ≤ 2047 ∧
      plonkSelectors.2.2.natDegree ≤ 2047 := by
  unfold plonkSelectors
  have h := canonicalLagrangePolynomials_natDegree_lt (n := 2048) (blinding := 5)
    (omegaOf 11) (by decide) (omegaOf_rows_injective 11 (by decide))
  exact ⟨Nat.le_of_lt_succ h.1, Nat.le_of_lt_succ h.2.1, Nat.le_of_lt_succ h.2.2⟩

/-- Zero-default indexed access preserves a uniform polynomial degree bound, including out-of-range
queries. -/
private theorem finFn_natDegree_le {n B : ℕ} (values : Fin n → CPoly)
    (hvalues : ∀ j, (values j).natDegree ≤ B) (i : ℕ) :
    (finFn values i).natDegree ≤ B := by
  by_cases hi : i < n
  · simpa only [finFn, dif_pos hi] using hvalues ⟨i, hi⟩
  · simp only [finFn, dif_neg hi, natDegree_zero, Nat.zero_le]

/-- Resolving any column reference preserves the shared degree bound, lifting column bounds to
verifier expressions. -/
private theorem resolve_natDegree_le {B : ℕ} (fx av inst : ℕ → CPoly)
    (hfx : ∀ i, (fx i).natDegree ≤ B) (hav : ∀ i, (av i).natDegree ≤ B)
    (hinst : ∀ i, (inst i).natDegree ≤ B) (cr : ColumnRef) :
    (cr.resolve inst av fx).natDegree ≤ B := by
  cases cr with
  | advice i => exact hav i
  | fixed i => exact hfx i
  | «instance» i => exact hinst i

/-- Degree accounting for a packaged constraint model, with separate lookup bounds. -/
theorem constraintModel_natDegree_le {actions B W Di Dt D : ℕ}
    (model : ConstraintPolyModel actions) (hB : 1 ≤ B)
    (hfx : ∀ i, (model.fixedCols i).natDegree ≤ B)
    (hav : ∀ a i, (model.adviceCols a i).natDegree ≤ B)
    (hinst : ∀ a i, (model.instanceCols a i).natDegree ≤ B)
    (hgates : ∀ e ∈ model.gates, e.degreeBound * B ≤ D)
    (hsets : ∀ a s, s ∈ model.sets a →
      s.eval.natDegree ≤ B ∧ (s.lastEval.getD 0).natDegree ≤ B)
    (hchunks : ∀ a c, c ∈ model.chunks a →
      (c.1.eval.natDegree ≤ B ∧ c.1.nextEval.natDegree ≤ B) ∧ c.2.length ≤ W ∧
        ∀ pair ∈ c.2, pair.1.natDegree ≤ B ∧ pair.2.natDegree ≤ B)
    (hlooks : ∀ a lk, lk ∈ model.lookups a →
      (lk.1.productEval.natDegree ≤ B ∧ lk.1.productNextEval.natDegree ≤ B ∧
        lk.1.permutedInputEval.natDegree ≤ B ∧ lk.1.permutedInputInvEval.natDegree ≤ B ∧
        lk.1.permutedTableEval.natDegree ≤ B) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * B ≤ Di) ∧ (∀ e ∈ lk.2.2, e.degreeBound * B ≤ Dt))
    (hl0 : model.l0.natDegree ≤ B) (hll : model.lLast.natDegree ≤ B)
    (hlb : model.lBlind.natDegree ≤ B)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D)
    (hcomp : 2 * B + Di + Dt ≤ D) :
    ∀ poly ∈ model.constraints, poly.natDegree ≤ D := by
  intro poly hpoly
  rw [ConstraintPolyModel.constraints] at hpoly
  obtain ⟨family, hfamily, hpoly⟩ := List.mem_flatten.mp hpoly
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hfamily
  rw [ConstraintPolyModel.subProofConstraints] at hpoly
  rcases List.mem_append.mp hpoly with hpoly | hpoly
  · rcases List.mem_append.mp hpoly with hpoly | hpoly
    · rw [ConstraintPolyModel.gateConstraints] at hpoly
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpoly
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp he
      exact le_trans (natDegree_eval_map_C_le hfx (hav a) (hinst a) original)
        (hgates original horiginal)
    · exact natDegree_permutationExpressions_le hB (model.sets a) (model.chunks a)
        model.beta model.gamma model.delta model.chunkLen model.l0 model.lLast model.lBlind
        (hsets a) (hchunks a) hl0 hll hlb h3 hWD poly hpoly
  · rw [ConstraintPolyModel.lookupConstraints] at hpoly
    obtain ⟨family, hfamily, hpoly⟩ := List.mem_flatten.mp hpoly
    obtain ⟨lk, hlk, rfl⟩ := List.mem_map.mp hfamily
    exact lookupExpressions_natDegree_le hfx (hav a) (hinst a) lk.1 lk.2.1 lk.2.2
      model.theta model.beta model.gamma model.l0 model.lLast model.lBlind
      (hlooks a lk hlk).1 (hlooks a lk hlk).2.1 (hlooks a lk hlk).2.2
      hl0 hll hlb h4 hcomp poly hpoly

/-- The public circuit profile bounds the numerator for every private row state. -/
theorem plonkConstraintNumerator_natDegree_le {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (profile : PlonkDegreeProfile vk)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048) :
    (plonkConstraintNumerator vk pub ch rows).natDegree ≤ 9 * 2047 := by
  let ps : ProofString (plonkProofShape actions k) CPoly G := plonkPolynomialClaimProof pub rows
  let model := plonkConstraintModel vk pub ch rows
  have hfx (i : ℕ) : (model.fixedCols i).natDegree ≤ 2047 := by
    apply finFn_natDegree_le
    intro j
    exact Nat.le_of_lt_succ (hfixed (plonkFixedQueryOrder j))
  have hav (a : Fin actions) (i : ℕ) : (model.adviceCols a i).natDegree ≤ 2047 := by
    apply finFn_natDegree_le
    intro j
    exact plonkRotatedColumn_natDegree_le rows (.advice a (plonkAdviceQueryOrder j).1)
      ((plonkAdviceQueryOrder j).2.castLE (by decide))
  have hinst (a : Fin actions) (i : ℕ) : (model.instanceCols a i).natDegree ≤ 2047 := by
    apply finFn_natDegree_le
    intro j
    exact Nat.le_of_lt_succ (hinstance a)
  have hcommon (i : ℕ) : (finFn ps.permutationCommonEvals i).natDegree ≤ 2047 :=
    finFn_natDegree_le pub.sigma (fun c => Nat.le_of_lt_succ (hsigma c)) i
  have hsets (a : Fin actions) (s : PermSetEval CPoly) (hs : s ∈ model.sets a) :
      s.eval.natDegree ≤ 2047 ∧ s.nextEval.natDegree ≤ 2047 ∧
        (s.lastEval.getD 0).natDegree ≤ 2047 := by
    change s ∈ List.ofFn (ps.permutationSetEvals a) at hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    refine ⟨plonkRotatedColumn_natDegree_le rows (.permutationProduct a j) 0,
      plonkRotatedColumn_natDegree_le rows (.permutationProduct a j) 1, ?_⟩
    change ((if j.val < 2 then some (plonkRotatedColumn rows (.permutationProduct a j) 3)
      else none).getD 0).natDegree ≤ 2047
    split
    · exact plonkRotatedColumn_natDegree_le rows (.permutationProduct a j) 3
    · simp
  have hchunks (a : Fin actions) (c : PermSetEval CPoly × List (CPoly × CPoly))
      (hc : c ∈ model.chunks a) :
      (c.1.eval.natDegree ≤ 2047 ∧ c.1.nextEval.natDegree ≤ 2047) ∧ c.2.length ≤ 7 ∧
        ∀ pair ∈ c.2, pair.1.natDegree ≤ 2047 ∧ pair.2.natDegree ≤ 2047 := by
    change c ∈ ((List.ofFn (ps.permutationSetEvals a)).zip vk.permutationChunks).map
      (fun sc => (sc.1, sc.2.map fun cr =>
        (cr.1.resolve (finFn (ps.instanceEvals a)) (finFn (ps.adviceEvals a)) (finFn ps.fixedEvals),
          finFn ps.permutationCommonEvals cr.2))) at hc
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hset, hchunk⟩ := List.of_mem_zip hsc
    have hsetBounds := hsets a sc.1 hset
    refine ⟨⟨hsetBounds.1, hsetBounds.2.1⟩, ?_, ?_⟩
    · simpa only [List.length_map] using profile.chunks sc.2 hchunk
    · intro pair hpair
      obtain ⟨cr, _, rfl⟩ := List.mem_map.mp hpair
      exact ⟨resolve_natDegree_le model.fixedCols (model.adviceCols a) (model.instanceCols a)
        hfx (hav a) (hinst a) cr.1, hcommon cr.2⟩
  have hlooks (a : Fin actions) (lk : LookupEval CPoly × List (Expr Fp) × List (Expr Fp))
      (hlk : lk ∈ model.lookups a) :
      (lk.1.productEval.natDegree ≤ 2047 ∧ lk.1.productNextEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputEval.natDegree ≤ 2047 ∧ lk.1.permutedInputInvEval.natDegree ≤ 2047 ∧
        lk.1.permutedTableEval.natDegree ≤ 2047) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * 2047 ≤ 4 * 2047) ∧
      (∀ e ∈ lk.2.2, e.degreeBound * 2047 ≤ 2047) := by
    change lk ∈ List.ofFn (fun l => (ps.lookupEvals a l, vk.lookupInputExprs l,
      vk.lookupTableExprs l)) at hlk
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
    refine ⟨⟨plonkRotatedColumn_natDegree_le rows (.lookupProduct a l) 0,
      plonkRotatedColumn_natDegree_le rows (.lookupProduct a l) 1,
      plonkRotatedColumn_natDegree_le rows (.lookupInput a l) 0,
      plonkRotatedColumn_natDegree_le rows (.lookupInput a l) 2,
      plonkRotatedColumn_natDegree_le rows (.lookupTable a l) 0⟩, ?_, ?_⟩
    · intro e he
      exact Nat.mul_le_mul_right 2047 (profile.inputs l e he)
    · intro e he
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right 2047 (profile.tables l e he)
  have hconstraints : ∀ poly ∈ model.constraints, poly.natDegree ≤ 9 * 2047 := by
    apply constraintModel_natDegree_le (B := 2047) (W := 7) (Di := 4 * 2047) (Dt := 2047)
      model (by decide) hfx hav hinst
    · intro e he
      exact Nat.mul_le_mul_right 2047 (profile.gates e he)
    · intro a s hs
      exact ⟨(hsets a s hs).1, (hsets a s hs).2.2⟩
    · exact hchunks
    · exact hlooks
    · exact plonkSelectors_natDegree_le.1
    · exact plonkSelectors_natDegree_le.2.1
    · exact plonkSelectors_natDegree_le.2.2
    all_goals decide
  rw [plonkConstraintNumerator_eq_fold]
  exact natDegree_foldByY_le ch.y model.constraints hconstraints

/-- The numerator always fits the capacity needed for eight quotient blocks. -/
theorem plonkConstraintNumerator_natDegree_lt {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (profile : PlonkDegreeProfile vk)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048) :
    (plonkConstraintNumerator vk pub ch rows).natDegree < 9 * 2048 :=
  lt_of_le_of_lt (plonkConstraintNumerator_natDegree_le vk pub ch rows profile hinstance hfixed hsigma)
    (by decide)

end Zcash.Snark.ZeroKnowledge
