import Zcash.Snark.ZeroKnowledge.PlonkConstructedConstraints
import Zcash.Snark.ZeroKnowledge.PlonkProductBounds

/-!
# The remaining row-construction prerequisites

Completed sorting, preservation of gates under masking, and the packed copy-product
identity are the remaining structural premises for numerator division. Nonzero
denominators are separate: their probability is now bounded for the computed scans.
Keeping these events distinct exposes what is still needed from a valid Orchard
witness and its public key without assuming that every random execution is valid.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial Finset

/-- The concrete construction conditions still needed in addition to nonzero denominators. -/
structure PlonkRowPrerequisites {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) : Prop where
  complete : (plonkColumnAttempt vk pub witness ch tape).complete = true
  gates : ∀ a : Fin actions,
    ∀ poly ∈ (plonkConstraintModel vk pub ch (plonkTotalColumnRows vk pub witness ch tape)).gateConstraints a,
      (X ^ 2048 - 1 : CPoly) ∣ poly
  copyProduct : ∀ a : Fin actions,
    (∏ c ∈ range 3, ∏ i ∈ range 2042,
      permutationRowNumerator
        (plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks)
        ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen c i) =
    ∏ c ∈ range 3, ∏ i ∈ range 2042,
      permutationRowDenominator
        (plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks)
        ch.beta ch.gamma c i

/-- The total reference numerator divides on the original tape once its explicit prerequisites hold. -/
theorem plonkTotalColumnRows_domain_division {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (hchunks : vk.permutationChunks.length = 3)
    (hready : PlonkRowPrerequisites vk pub witness ch tape)
    (hden : plonkProductDenominatorsNonzero pub (plonkTotalColumnRows vk pub witness ch tape)
      vk.permutationChunks ch.beta ch.gamma) :
    (X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch (plonkTotalColumnRows vk pub witness ch tape) := by
  have hrows := plonkColumnAttempt_eq_totalRows_of_complete vk pub witness ch tape hready.complete
  have h := plonkColumnAttempt_domain_division vk pub witness ch tape hready.complete hchunks
    (by simpa only [hrows] using hready.gates)
    (by simpa only [hrows] using hready.copyProduct)
    (fun a c hc i hi => by
      simpa only [hrows] using hden.1 a c (by simpa only [hchunks] using hc) i hi)
    (fun a l i hi => by
      simpa only [hrows] using hden.2 a l ⟨i, hi⟩)
  simpa only [hrows] using h.2

/-- Every invalid reference numerator is covered by a failed prerequisite or a zero denominator. -/
theorem plonkTotalColumnRows_invalid_cover {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (hchunks : vk.permutationChunks.length = 3)
    (hbad : ¬ (X ^ 2048 - 1 : CPoly) ∣
      plonkConstraintNumerator vk pub ch (plonkTotalColumnRows vk pub witness ch tape)) :
    ¬ PlonkRowPrerequisites vk pub witness ch tape ∨
      ¬ plonkProductDenominatorsNonzero pub (plonkTotalColumnRows vk pub witness ch tape)
        vk.permutationChunks ch.beta ch.gamma := by
  classical
  by_cases hready : PlonkRowPrerequisites vk pub witness ch tape
  · exact Or.inr fun hden => hbad (plonkTotalColumnRows_domain_division vk pub witness ch tape hchunks hready hden)
  · exact Or.inl hready

end Zcash.Snark.ZeroKnowledge
