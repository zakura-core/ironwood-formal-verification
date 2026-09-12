import Zcash.Snark.ZeroKnowledge.TranscriptScheduleCost
import Zcash.Snark.ZeroKnowledge.PlonkTranscriptSize

/-! # Exact collection costs and original schedule sizes -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Collection pays exactly for block producers, their output cells, and five units per block. -/
theorem concatTranscriptBlocksCosted_cost {α : Type*} (blocks : List (List α × ℕ)) :
    (concatTranscriptBlocksCosted blocks).2 =
      (blocks.map Prod.snd).sum + (concatTranscriptBlocksCosted blocks).1.length + 5 * blocks.length + 1 := by
  rw [concatTranscriptBlocksCosted_result]
  unfold concatTranscriptBlocksCosted
  induction blocks with
  | nil => rfl
  | cons first rest ih =>
    simp only [flatMapListCosted, appendListCosted_cost, List.map_cons, List.sum_cons,
      List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- The evaluation block includes at most the original fifty per-Action and forty-five shared claims. -/
theorem proofEvaluationBlocksCosted_length_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) :
    (proofEvaluationBlocksCosted proof).1.length ≤ 50 * actions + 45 := by
  have hperm : ((List.ofFn fun a =>
      (List.ofFn fun s =>
        absorbPermSet (G := G) ((proof.permutationSetEvals a s).map Prod.fst)).flatten)).flatten.length
        ≤ actions * 9 := by
    apply length_flatten_ofFn_le
    intro action
    apply length_flatten_ofFn_le (width := 3)
    intro set
    rw [← absorbPermSetCosted_result]
    exact absorbPermSetCosted_length_le _
  simp only [proofEvaluationBlocksCosted, concatTranscriptBlocksCosted_result,
    List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons, List.length_nil,
    absorbScalarsCosted_result, absorbScalars2Costed_result, flattenFinCosted_result,
    absorbPermSetCosted_result, absorbLookupCosted_result,
    absorbScalars, absorbScalars2, absorbLookup,
    List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn] at hperm ⊢
  simp only [plonkProofShape, FixtureMax.shape, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hperm ⊢
  simp only [Fintype.card_eq_nat_card, Nat.card_fin] at hperm ⊢
  omega

/-- The counted pre-IPA constructor preserves the original size bound at every optional-field branch. -/
theorem preIpaTranscriptCosted_length_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) :
    (preIpaTranscriptCosted proof).1.length ≤ 72 * actions + 72 := by
  rw [preIpaTranscriptCosted_result]
  exact plonkPreIpaTranscript_length_le _

/-- The complete counted attempt retains the original linear item envelope. -/
theorem plonkAttemptTraceCosted_length_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) :
    (plonkAttemptTraceCosted proof).1.length ≤ 72 * actions + 3 * k + 74 := by
  rw [plonkAttemptTraceCosted_result]
  exact plonkAttemptTrace_length_le _

end Zcash.Snark.ZeroKnowledge
