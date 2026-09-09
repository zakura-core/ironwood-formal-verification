import Zcash.Snark.ZeroKnowledge.ProofFieldReadCost
import Zcash.Snark.ZeroKnowledge.PlonkAttempt

/-!
# Counted construction of the complete original message schedule

All field producers are forced while constructing the typed transcript. The
result theorem retains every original point, scalar, and challenge marker,
including the two final responses and every optional permutation claim. A
later observer can stop on an exceptional value without making this complete
construction cost disappear.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Concatenate produced blocks, including their preparation and block-list cells. -/
def concatTranscriptBlocksCosted {α : Type*} (blocks : List (List α × ℕ)) : List α × ℕ :=
  flatMapListCosted (fun block => (block.1, block.2 + 3)) blocks

/-- Concatenation preserves all block contents and their order. -/
theorem concatTranscriptBlocksCosted_result {α : Type*} (blocks : List (List α × ℕ)) :
    (concatTranscriptBlocksCosted blocks).1 = blocks.flatMap Prod.fst :=
  flatMapListCosted_result _ _

/-- Every block producer, copied output cell, and block-list cell remains in the bound. -/
theorem concatTranscriptBlocksCosted_cost_le {α : Type*} (blocks : List (List α × ℕ)) :
    (concatTranscriptBlocksCosted blocks).2 ≤
      (blocks.map (fun block => block.2 + 3 + block.1.length + 2)).sum + 1 := by
  exact flatMapListCosted_cost_le_sum (fun block : List α × ℕ => (block.1, block.2 + 3)) blocks
    (fun block => block.2 + 3) (fun block => block.1.length) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

/-- Produce every PLONK evaluation in the verifier's original disclosure order. -/
def proofEvaluationBlocksCosted {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) : List (TranscriptElt F G) × ℕ :=
  concatTranscriptBlocksCosted
    [absorbScalars2Costed proof.instanceEvals,
      absorbScalars2Costed proof.adviceEvals,
      absorbScalarsCosted proof.fixedEvals,
      ([.scalar proof.vanishingRandomEval.1], proof.vanishingRandomEval.2 + 2),
      absorbScalarsCosted proof.permutationCommonEvals,
      flattenFinCosted (fun action => flattenFinCosted (fun set =>
        absorbPermSetCosted (proof.permutationSetEvals action set))),
      flattenFinCosted (fun action => flattenFinCosted (fun lookup =>
        absorbLookupCosted (proof.lookupEvals action lookup)))]

/-- Produce the complete pre-IPA schedule with all eleven original challenge markers. -/
def preIpaTranscriptCosted {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) : List (TranscriptElt F G) × ℕ :=
  concatTranscriptBlocksCosted
    [absorbPoints2Costed proof.adviceCommitments,
      ([.challenge], 2),
      absorbLookupPermutedCosted proof.lookupPermutedInput proof.lookupPermutedTable,
      ([.challenge, .challenge], 3),
      absorbPoints2Costed proof.permutationProduct,
      absorbPoints2Costed proof.lookupProduct,
      ([.point proof.vanishingRandom.1], proof.vanishingRandom.2 + 2),
      ([.challenge], 2),
      absorbPointsCosted proof.hPieces,
      ([.challenge], 2),
      proofEvaluationBlocksCosted proof,
      ([.challenge, .challenge], 3),
      ([.point proof.multiopenQPrime.1], proof.multiopenQPrime.2 + 2),
      ([.challenge], 2),
      absorbScalarsCosted proof.multiopenU,
      ([.challenge], 2),
      ([.point proof.ipaS.1], proof.ipaS.2 + 2),
      ([.challenge, .challenge], 3)]

/-- The complete counted prefix is the actual verifier's pre-IPA transcript. -/
theorem preIpaTranscriptCosted_result {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) :
    (preIpaTranscriptCosted proof).1 = preIpaTranscript [] (eraseProofCosts proof) := by
  simp only [preIpaTranscriptCosted, proofEvaluationBlocksCosted,
    concatTranscriptBlocksCosted_result, List.flatMap_cons, List.flatMap_nil,
    absorbPoints2Costed_result, absorbScalars2Costed_result,
    absorbPointsCosted_result, absorbScalarsCosted_result,
    absorbLookupPermutedCosted_result, flattenFinCosted_result,
    absorbPermSetCosted_result, absorbLookupCosted_result,
    preIpaTranscript, eraseProofCosts, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]

/-- Force all original IPA point pairs and challenge markers in round order. -/
def ipaRoundBlocksCosted {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) : List (TranscriptElt F G) × ℕ :=
  flattenFinCosted (fun round =>
    let pair := proof.ipaRounds round
    ([.point pair.1.1, .point pair.2.1, .challenge], pair.1.2 + pair.2.2 + 7))

/-- The counted IPA blocks have exactly the original round order. -/
theorem ipaRoundBlocksCosted_result {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) :
    (ipaRoundBlocksCosted proof).1 =
      (List.ofFn (fun round => [TranscriptElt.point (proof.ipaRounds round).1.1,
        .point (proof.ipaRounds round).2.1, .challenge])).flatten :=
  flattenFinCosted_result _

/-- Construct every message and marker in the complete specified attempt. -/
def plonkAttemptTraceCosted {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) : List (TranscriptElt F G) × ℕ :=
  concatTranscriptBlocksCosted
    [preIpaTranscriptCosted proof, ipaRoundBlocksCosted proof,
      ([.scalar proof.ipaC.1, .scalar proof.ipaF.1], proof.ipaC.2 + proof.ipaF.2 + 5)]

/-- Full erasure equals the actual attempt schedule, including its two final scalar responses. -/
theorem plonkAttemptTraceCosted_result {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) :
    (plonkAttemptTraceCosted proof).1 = plonkAttemptTrace (eraseProofCosts proof) := by
  simp only [plonkAttemptTraceCosted, concatTranscriptBlocksCosted_result,
    List.flatMap_cons, List.flatMap_nil, preIpaTranscriptCosted_result,
    ipaRoundBlocksCosted_result, plonkAttemptTrace, eraseProofCosts,
    List.append_nil, List.append_assoc]
  rfl

end Zcash.Snark.ZeroKnowledge
