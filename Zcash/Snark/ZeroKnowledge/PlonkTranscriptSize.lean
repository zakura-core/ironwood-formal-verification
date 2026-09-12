import Zcash.Snark.ZeroKnowledge.PlonkAttempt
import Zcash.Snark.ZeroKnowledge.TranscriptByteSize

/-!
# A linear size envelope for the complete PLONK and IPA schedule

The bound follows the existing verifier's absorb order. It even permits a last
evaluation in every permutation set, so it needs no proof well-formedness or
successful-emission premise. The simulator's more restrictive layout is covered.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Concatenating a bounded-width finite family has at most count times width elements. -/
theorem length_flatten_ofFn_le {α : Type*} {count : ℕ} (items : Fin count → List α)
    (width : ℕ) (hwidth : ∀ i, (items i).length ≤ width) :
    (List.ofFn items).flatten.length ≤ count * width := by
  simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  exact (Finset.sum_le_sum fun i _ => hwidth i).trans_eq (by simp)

/-- The actual pre-IPA layout is linear in Action count, even with every optional evaluation. -/
theorem plonkPreIpaTranscript_length_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) :
    (preIpaTranscript [] proof).length ≤ 72 * actions + 72 := by
  have hperm : ((List.ofFn fun a =>
      (List.ofFn fun s => absorbPermSet (G := G) (proof.permutationSetEvals a s)).flatten)).flatten.length
        ≤ actions * 9 := by
    apply length_flatten_ofFn_le
    intro a
    apply length_flatten_ofFn_le (width := 3)
    intro s
    cases h : (proof.permutationSetEvals a s).lastEval <;> simp [absorbPermSet, h]
  simp only [preIpaTranscript, List.length_append, List.length_cons, List.length_nil,
    absorbPoints, absorbPoints2, absorbScalars, absorbScalars2, absorbLookupPermuted,
    absorbLookup, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn,
    List.sum_ofFn] at hperm ⊢
  simp only [plonkProofShape, FixtureMax.shape, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hperm ⊢
  simp only [Fintype.card_eq_nat_card, Nat.card_fin] at hperm ⊢
  omega

/-- The full trace adds two round points and one challenge per IPA round, then two scalars. -/
theorem plonkAttemptTrace_length_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) :
    (plonkAttemptTrace proof).length ≤ 72 * actions + 3 * k + 74 := by
  have h := plonkPreIpaTranscript_length_le proof
  simp only [plonkAttemptTrace, List.length_append, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.length_cons, List.length_nil, List.sum_ofFn, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- Every raw-hash address has a linear byte-size envelope in public initialization and Action count. -/
theorem plonkQueryAddress_bytes_le {actions k : ℕ}
    (initial : List (TranscriptElt Fp VestaG))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) (index : ℕ) :
    (protocolQueryAddress initial (plonkAttemptTrace proof) index).1.length +
      (protocolQueryAddress initial (plonkAttemptTrace proof) index).2.length ≤
      16 + 65 * (initial.length + 72 * actions + 3 * k + 75) := by
  exact (protocolQueryAddress_bytes_le initial (plonkAttemptTrace proof) index).trans
    (by have h := plonkAttemptTrace_length_le proof; omega)

end Zcash.Snark.ZeroKnowledge
