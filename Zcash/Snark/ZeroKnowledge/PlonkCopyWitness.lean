import Zcash.Snark.ZeroKnowledge.PlonkCopyCells

/-!
# From original witness copies to the computed product identity

These premises concern the supplied witness and public key, before any masks or
challenges are sampled. The sigma premise relates public polynomial labels to the
replay of an explicit usable-cell copy list. Masking preserves those copy equations,
so the computed product identity holds on every tape, including zero denominators.
PlonkKeygenCopies supplies this usable-cell list from the compiler's ordered copy
stream, and PlonkKeygenSigma derives the public-label coherence from key generation.
ActionWitnessSimulation supplies constructed witness values for the Action application;
ActionDerivedKey and ActionCommitments supply its key layout and public commitments.
Whole-program Rust correspondence is outside these reference-model results.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Finset

/-- Original copy equations and public sigma coherence for the concrete packed layout. -/
structure PlonkCopyWitness {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks)) : Prop where
  unrotated : plonkPermutationQueriesUnrotated vk.permutationChunks = true
  sigma : ∀ cell, plonkCopyCellSigma pub cell =
    plonkCopyCellName vk.delta vk.chunkLen (replayKeygenPermutation copies cell)
  values : ∀ a : Fin actions, ∀ pair ∈ copies,
    (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1

/-- The masked factors satisfy every declared original copy equation on every tape. -/
theorem plonkCopyWitness_masked {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) :
    ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks pair.2).1 := by
  intro pair hpair
  rw [plonkCopyCellPair_masked vk pub witness ch tape hcopy.unrotated,
    plonkCopyCellPair_masked vk pub witness ch tape hcopy.unrotated]
  exact hcopy.values a pair hpair

/-- Original copies imply the exact packed product identity used by the computed scans. -/
theorem plonkTotalColumnRows_copyProduct {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) :
    (∏ c ∈ range 3, ∏ i ∈ range 2042,
      permutationRowNumerator
        (plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks)
        ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range 2042,
        permutationRowDenominator
          (plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks)
          ch.beta ch.gamma c i := by
  classical
  rw [plonkPermutationNumerator_prod_cells, plonkPermutationDenominator_prod_cells]
  simp_rw [plonkCopyCellPair_sigma, hcopy.sigma]
  apply copyPermutation_product_identity
  exact copyValues_replay copies
    (fun cell => (plonkCopyCellPair pub (plonkTotalColumnRows vk pub witness ch tape)
      a vk.permutationChunks cell).1)
    (plonkCopyWitness_masked vk pub witness copies hcopy ch tape a)

end Zcash.Snark.ZeroKnowledge
