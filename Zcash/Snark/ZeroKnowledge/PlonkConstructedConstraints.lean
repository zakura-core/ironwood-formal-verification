import Zcash.Snark.ZeroKnowledge.PlonkConstructedLookup
import Zcash.Snark.ZeroKnowledge.PlonkConstructedPermutation

/-!
# Domain division for the executed column schedule

The lookup and permutation construction theorems discharge the product-argument
constraints of the actual final column state. Combining them with the gate
constraints gives divisibility of every constraint and of the computed numerator.

The remaining premises are explicit: completed construction, gate correctness after
masking, the packed copy-product identity, and nonzero active denominator factors.
This does not yet derive these conditions from the supplied satisfying advice or
bound the probability of exceptional random tapes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial Finset

/-- The concrete schedule's product constraints supply exact numerator division, given gates and copy identity. -/
theorem plonkColumnAttempt_domain_division {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (hchunks : vk.permutationChunks.length = 3)
    (hgate : ∀ a : Fin actions,
      ∀ poly ∈ (plonkConstraintModel vk pub ch (plonkColumnAttempt vk pub witness ch tape).columns).gateConstraints a,
        (X ^ 2048 - 1 : CPoly) ∣ poly)
    (hproduct : ∀ a : Fin actions,
      (∏ c ∈ range 3, ∏ i ∈ range 2042,
        permutationRowNumerator
          (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
          ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range 2042,
        permutationRowDenominator
          (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
          ch.beta ch.gamma c i)
    (hpermutationDen : ∀ a : Fin actions, ∀ c < 3, ∀ i < 2042,
      permutationRowDenominator
        (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
        ch.beta ch.gamma c i ≠ 0)
    (hlookupDen : ∀ a : Fin actions, ∀ l : Fin 3, ∀ i < 2042,
      (privateColumnPolynomial (plonkColumnAttempt vk pub witness ch tape).columns (.lookupInput a l)).eval
          (omegaOf 11 ^ i) + ch.beta ≠ 0 ∧
      (privateColumnPolynomial (plonkColumnAttempt vk pub witness ch tape).columns (.lookupTable a l)).eval
          (omegaOf 11 ^ i) + ch.gamma ≠ 0) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    (∀ poly ∈ (plonkConstraintModel vk pub ch rows).constraints, (X ^ 2048 - 1 : CPoly) ∣ poly) ∧
      (X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows := by
  let rows := (plonkColumnAttempt vk pub witness ch tape).columns
  let model := plonkConstraintModel vk pub ch rows
  have hpermutation (a : Fin actions) :
      ∀ poly ∈ model.permutationConstraints a, (X ^ 2048 - 1 : CPoly) ∣ poly :=
    plonkColumnAttempt_permutationConstraints_dvd vk pub witness ch tape hcomplete a hchunks
      (hproduct a) (hpermutationDen a)
  have hlookup (a : Fin actions) :
      ∀ poly ∈ model.lookupConstraints a, (X ^ 2048 - 1 : CPoly) ∣ poly :=
    plonkColumnAttempt_lookupConstraints_dvd vk pub witness ch tape hcomplete a (hlookupDen a)
  have hall : ∀ poly ∈ model.constraints, (X ^ 2048 - 1 : CPoly) ∣ poly := by
    intro poly hpoly
    unfold ConstraintPolyModel.constraints at hpoly
    obtain ⟨entries, hentries, hpoly⟩ := List.mem_flatten.mp hpoly
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hentries
    change poly ∈ model.gateConstraints a ++ model.permutationConstraints a ++ model.lookupConstraints a at hpoly
    rcases List.mem_append.mp hpoly with hgp | hl
    · rcases List.mem_append.mp hgp with hg | hp
      · exact hgate a poly hg
      · exact hpermutation a poly hp
    · exact hlookup a poly hl
  refine ⟨hall, ?_⟩
  apply plonkConstraintNumerator_dvd_of_rows vk pub ch rows
  intro poly hpoly
  exact rows_zero_of_domainPolynomial_dvd (omegaOf 11)
    (omegaOf_primitiveRoot 11 (by decide)).pow_eq_one poly (hall poly hpoly)

end Zcash.Snark.ZeroKnowledge
