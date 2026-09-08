import Zcash.Snark.ZeroKnowledge.StageQuery
import Zcash.Snark.ZeroKnowledge.PlonkStageCausality

/-!
# Sealing every oracle query to the existing verifier

The complete trace's challenge prefixes are exactly the inputs read by
`deriveChallenges`: the eleven PLONK/multi-opening queries followed by each IPA
round. This also covers empty message stages between consecutive challenges.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The stage list splits at precisely the original pre-IPA/IPA boundary. -/
theorem plonkStageBlocks_split {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) :
    List.ofFn (fun j : Fin (11 + k) => plonkStageMessages proof j ++ [.challenge]) =
      List.ofFn (fun j => plonkPreIpaStages proof j ++ [.challenge]) ++
        List.ofFn (fun j : Fin k => [.point (proof.ipaRounds j).1, .point (proof.ipaRounds j).2, .challenge]) := by
  rw [List.ofFn_add (n := 11) (m := k)]
  refine congrArg₂ List.append ?_ ?_
  · apply congrArg List.ofFn
    funext j
    change plonkStageMessages proof (Fin.castAdd k j) ++ [.challenge] = _
    apply congrArg (fun block : List (TranscriptElt F G) =>
      block ++ [TranscriptElt.challenge (F := F) (G := G)])
    unfold plonkStageMessages
    exact Fin.addCases_left j
  · apply congrArg List.ofFn
    funext j
    change plonkStageMessages proof (Fin.natAdd 11 j) ++ [.challenge] = _
    simp only [plonkStageMessages, Fin.addCases_right, List.cons_append, List.nil_append]

/-- The pre-IPA message blocks concatenate to the existing verifier prefix. -/
theorem plonkPreIpaBlocks_transcript {shape : Shape} {F G : Type*}
    (initial : List (TranscriptElt F G)) (proof : ProofString shape F G) :
    initial ++ (List.ofFn (fun j => plonkPreIpaStages proof j ++ [.challenge])).flatten =
      preIpaTranscript initial proof := by
  simp [plonkPreIpaStages, plonkEvaluationStage, List.ofFn_succ, preIpaTranscript, List.append_assoc]

/-- A pre-IPA query contains exactly its first message blocks. -/
theorem plonkQueryPrefix_preIpa {actions k : ℕ} {F G : Type*}
    (initial : List (TranscriptElt F G)) (proof : ProofString (plonkProofShape actions k) F G)
    (index : Fin 11) :
    protocolQueryPrefix initial (plonkAttemptTrace proof) index.val =
      initial ++ ((List.ofFn (fun j => plonkPreIpaStages proof j ++ [.challenge])).take (index.val + 1)).flatten := by
  rw [plonkAttemptTrace_eq_stages,
    protocolQueryPrefix_stages (11 + k) initial _ _ (plonkStageMessages_challengeCount proof)
      ⟨index.val, by omega⟩, plonkStageBlocks_split proof]
  rw [List.take_append_of_le_length (by simp only [List.length_ofFn]; omega)]

/-- Every IPA query is the verifier's round transcript, including that round's two points. -/
theorem plonkQueryPrefix_ipaRound {actions k : ℕ} {F G : Type*}
    (initial : List (TranscriptElt F G)) (proof : ProofString (plonkProofShape actions k) F G)
    (round : Fin k) :
    protocolQueryPrefix initial (plonkAttemptTrace proof) (11 + round.val) =
      roundTranscriptFin (preIpaTranscript initial proof) proof.ipaRounds round := by
  rw [plonkAttemptTrace_eq_stages,
    protocolQueryPrefix_stages (11 + k) initial _ _ (plonkStageMessages_challengeCount proof)
      ⟨11 + round.val, by omega⟩, plonkStageBlocks_split proof, List.take_append]
  rw [List.take_of_length_le (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn]
  have hsub : 11 + round.val + 1 - 11 = round.val + 1 := by omega
  rw [hsub, List.flatten_append, ← List.append_assoc, plonkPreIpaBlocks_transcript]
  simp only [roundTranscriptFin, List.ofFn_eq_map, ← List.map_take]
  rfl

/-- The existing verifier reads each of its eleven pre-IPA challenges at the trace's same prefix. -/
theorem deriveChallenges_protocolQuery_preIpa {actions k : ℕ} {G : Type*}
    (fs : FiatShamir Fp G) (initial : List (TranscriptElt Fp G))
    (proof : ProofString (plonkProofShape actions k) Fp G) (index : Fin 11) :
    plonkAttemptChallenge (deriveChallenges fs initial proof) index.val =
      fs.squeeze (protocolQueryPrefix initial (plonkAttemptTrace proof) index.val) := by
  rw [plonkQueryPrefix_preIpa]
  fin_cases index <;>
    simp [plonkAttemptChallenge, plonkChallengeSequence, deriveChallenges,
      plonkPreIpaStages, plonkEvaluationStage, List.ofFn_succ, List.append_assoc]

/-- All scheduled receives, including every IPA round, use exactly the verifier's challenge derivation. -/
theorem deriveChallenges_protocolQuery {actions k : ℕ} {G : Type*}
    (fs : FiatShamir Fp G) (initial : List (TranscriptElt Fp G))
    (proof : ProofString (plonkProofShape actions k) Fp G) (index : Fin (k + 11)) :
    plonkAttemptChallenge (deriveChallenges fs initial proof) index.val =
      fs.squeeze (protocolQueryPrefix initial (plonkAttemptTrace proof) index.val) := by
  by_cases hpre : index.val < 11
  · exact deriveChallenges_protocolQuery_preIpa fs initial proof ⟨index.val, hpre⟩
  · let round : Fin k := ⟨index.val - 11, by omega⟩
    have hindex : index.val = 11 + round.val := by dsimp [round]; omega
    rw [hindex]
    calc
      _ = (deriveChallenges fs initial proof).ipaRound round :=
        plonkAttemptChallenge_round (deriveChallenges fs initial proof) round
      _ = fs.squeeze (roundTranscriptFin (preIpaTranscript initial proof) proof.ipaRounds round) :=
        deriveChallenges_ipaRound_eq fs initial proof round
      _ = _ := congrArg fs.squeeze (plonkQueryPrefix_ipaRound initial proof round).symm

/-- Raw byte-oracle answers at every query reduce to exactly the verifier's field challenge. -/
theorem byteFiatShamir_protocolQuery {actions k : ℕ}
    (oracle : TranscriptHashAddress → Fin challengeDigestCard)
    (initial : List (TranscriptElt Fp VestaG))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) (index : Fin (k + 11)) :
    plonkAttemptChallenge (deriveChallenges (byteFiatShamir oracle) initial proof) index.val =
      ((oracle (protocolQueryAddress initial (plonkAttemptTrace proof) index.val)).val : Fp) :=
  deriveChallenges_protocolQuery _ _ _ _

end Zcash.Snark.ZeroKnowledge
