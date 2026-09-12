import Zcash.Snark.ZeroKnowledge.PlonkConstructedRows
import Zcash.Snark.ZeroKnowledge.PlonkLookupRows

/-!
# The executed lookup construction satisfies the actual lookup constraints

A completed column attempt supplies the compression feeds, both sorted-column
permutations, the run structure, and the product scan in the final polynomial state.
Outside zero active-row denominator factors, all fifteen lookup constraint
polynomials for each Action are therefore divisible by the domain polynomial.

No lookup sorting or scan agreement is assumed. Completion and the nonzero-factor
event remain explicit; this theorem does not bound either exceptional probability.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial

/-- Every lookup constraint of a completed reference attempt vanishes on the domain off zero factors. -/
theorem plonkColumnAttempt_lookupConstraints_dvd {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions)
    (hden : ∀ l : Fin 3, ∀ i < 2042,
      (privateColumnPolynomial (plonkColumnAttempt vk pub witness ch tape).columns (.lookupInput a l)).eval
          (omegaOf 11 ^ i) + ch.beta ≠ 0 ∧
      (privateColumnPolynomial (plonkColumnAttempt vk pub witness ch tape).columns (.lookupTable a l)).eval
          (omegaOf 11 ^ i) + ch.gamma ≠ 0) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    ∀ poly ∈ (plonkConstraintModel vk pub ch rows).lookupConstraints a,
      (X ^ 2048 - 1 : CPoly) ∣ poly := by
  let rows := (plonkColumnAttempt vk pub witness ch tape).columns
  let model := plonkConstraintModel vk pub ch rows
  change ∀ poly ∈ model.lookupConstraints a, (X ^ 2048 - 1 : CPoly) ∣ poly
  intro poly hpoly
  unfold ConstraintPolyModel.lookupConstraints at hpoly
  rw [plonkConstraintModel_lookups vk pub ch rows a] at hpoly
  obtain ⟨pieces, hpieces, hpoly⟩ := List.mem_flatten.mp hpoly
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hpieces
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hentry
  let input := plonkLookupCompressedRows pub rows ch.theta a (vk.lookupInputExprs l)
  let table := plonkLookupCompressedRows pub rows ch.theta a (vk.lookupTableExprs l)
  let zpoly := privateColumnPolynomial rows (.lookupProduct a l)
  let bpoly := privateColumnPolynomial rows (.lookupInput a l)
  let tpoly := privateColumnPolynomial rows (.lookupTable a l)
  obtain ⟨b, t, hsort, hb, ht⟩ := plonkColumnAttempt_lookup_sorted vk pub witness ch tape hcomplete a l
  obtain ⟨_, _, hinputPerm, htablePerm, hfirst, hrun⟩ :=
    lookupSortedPrefixes_correct 2042 input table b t hsort
  have hbList : (List.ofFn fun i : Fin 2042 => bpoly.eval (omegaOf 11 ^ i.val)) =
      (List.ofFn fun i : Fin 2042 => b.getD i.val 0) := by
    apply congrArg List.ofFn
    funext i
    exact hb i.val i.isLt
  have htList : (List.ofFn fun i : Fin 2042 => tpoly.eval (omegaOf 11 ^ i.val)) =
      (List.ofFn fun i : Fin 2042 => t.getD i.val 0) := by
    apply congrArg List.ofFn
    funext i
    exact ht i.val i.isLt
  have hinputPerm' : (List.ofFn fun i : Fin 2042 => input i.val).Perm
      (List.ofFn fun i : Fin 2042 => bpoly.eval (omegaOf 11 ^ i.val)) := by
    rw [hbList]
    exact hinputPerm
  have htablePerm' : (List.ofFn fun i : Fin 2042 => table i.val).Perm
      (List.ofFn fun i : Fin 2042 => tpoly.eval (omegaOf 11 ^ i.val)) := by
    rw [htList]
    exact htablePerm
  have hfirst' : bpoly.eval (omegaOf 11 ^ 0) = tpoly.eval (omegaOf 11 ^ 0) := by
    rw [hb 0 (by decide), ht 0 (by decide)]
    exact hfirst
  have hrun' (i : ℕ) (hpos : 0 < i) (hi : i < 2042) :
      bpoly.eval (omegaOf 11 ^ i) = tpoly.eval (omegaOf 11 ^ i) ∨
        bpoly.eval (omegaOf 11 ^ i) = bpoly.eval (omegaOf 11 ^ (i - 1)) := by
    rw [hb i hi, ht i hi, hb (i - 1) (by omega)]
    exact hrun i hpos hi
  have hdiv := lookupExpressions_dvd_domain_of_scan (n := 2048) (omegaOf 11)
    (by decide) (omegaOf_primitiveRoot 11 (by decide)) 2042 input table zpoly bpoly tpoly
    (vk.lookupInputExprs l) (vk.lookupTableExprs l)
    model.fixedCols (model.adviceCols a) (model.instanceCols a) ch.theta ch.beta ch.gamma plonkSelectors
    plonkSelectors_eval_row
    (fun i _ => (plonkLookupCompressedRows_eq_model vk pub ch rows a (vk.lookupInputExprs l) i).symm)
    (fun i _ => (plonkLookupCompressedRows_eq_model vk pub ch rows a (vk.lookupTableExprs l) i).symm)
    (fun i hi => plonkColumnAttempt_lookup_scan vk pub witness ch tape hcomplete a l i hi)
    hinputPerm' htablePerm' hfirst' hrun' (hden l)
  exact hdiv poly hpoly

end Zcash.Snark.ZeroKnowledge
