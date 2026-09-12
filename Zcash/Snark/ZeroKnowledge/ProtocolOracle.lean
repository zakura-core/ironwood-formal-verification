import Zcash.Snark.ZeroKnowledge.OracleSchedule
import Zcash.Snark.ZeroKnowledge.TranscriptQuery

/-!
# Causal oracle execution of the existing attempt observer

Before a squeeze the prover computes its already determined message prefix and
applies the existing encoding and failure checks. A failed prefix stops without
another query. A completed prefix appends the challenge marker and asks the raw
oracle. The independent replay retains the exact original attempt result.

The common public initialization is fixed by the caller and contributes no proof
bytes. This module does not establish the admissibility of that public prefix.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Only an attempt prefix without a failure can receive another scheduled challenge. -/
def protocolAttemptContinues (result : ProverAttemptResult) : Bool := decide (result.status = .complete)

/-- Apply the actual codecs and post-challenge checks to the messages already due. -/
def protocolOracleReport (pointCodec : VestaG → Option (List UInt8))
    (digests : ℕ → Fin challengeDigestCard) (check : ℕ → Option ProverAttemptFailure)
    (trace : List (TranscriptElt Fp VestaG)) (index : ℕ) : ProverAttemptResult :=
  observeProtocolTrace pointCodec plonkScalarCodec (fun i => ((digests i).val : Fp)) check 0
    (protocolPrefix index trace)

/-- Once a prefix fails, its retained result is already the complete attempt observation. -/
theorem protocolOracleReport_stopped (pointCodec : VestaG → Option (List UInt8))
    (digests : ℕ → Fin challengeDigestCard) (check : ℕ → Option ProverAttemptFailure)
    (trace : List (TranscriptElt Fp VestaG)) (index : ℕ)
    (hstop : protocolAttemptContinues (protocolOracleReport pointCodec digests check trace index) = false) :
    protocolOracleReport pointCodec digests check trace index =
      observeProtocolTrace pointCodec plonkScalarCodec (fun i => ((digests i).val : Fp)) check 0 trace := by
  have hfailed : (protocolOracleReport pointCodec digests check trace index).status ≠ .complete := by
    simpa only [protocolAttemptContinues, decide_eq_false_iff_not] using hstop
  obtain ⟨rest, hrest⟩ := protocolPrefix_isPrefix index trace
  have h := observeProtocolTrace_append_of_failed pointCodec plonkScalarCodec
    (fun i => ((digests i).val : Fp)) check 0 (protocolPrefix index trace) rest hfailed
  rw [hrest] at h
  exact h.symm

/-- Replay a complete independent digest tape and retain precisely the queried oracle prefix. -/
def protocolOracleView (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (trace : List (TranscriptElt Fp VestaG)) :
    ProverAttemptResult × List (TranscriptHashAddress × Fin challengeDigestCard) :=
  replayOracleSchedule (protocolOracleReport pointCodec digests check trace) protocolAttemptContinues
    (protocolQueryAddress initial trace) digests (protocolChallengeCount trace) 0

/-- Oracle replay preserves all original proof bytes, received field values, and failure status. -/
theorem protocolOracleView_result (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (trace : List (TranscriptElt Fp VestaG)) :
    (protocolOracleView pointCodec initial digests check trace).1 =
      observeProtocolTrace pointCodec plonkScalarCodec (fun i => ((digests i).val : Fp)) check 0 trace := by
  apply replayOracleSchedule_result
  · simp only [Nat.zero_add, protocolOracleReport,
      protocolPrefix_eq_of_count_le _ _ le_rfl]
  · intro i _ _ hstop
    exact protocolOracleReport_stopped pointCodec digests check trace i hstop

/-- Every query in an observed attempt has a distinct raw-hash address. -/
theorem protocolOracleView_queries_nodup (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (trace : List (TranscriptElt Fp VestaG)) :
    ((protocolOracleView pointCodec initial digests check trace).2.map Prod.fst).Nodup :=
  replayOracleSchedule_queries_nodup _ _ _ _ _ _
    (protocolQueryAddresses_nodup initial trace _ 0 (by omega))

/-- A query from a trace beginning with a private point retains that point as its anchor. -/
theorem protocolOracleView_queries_anchor (pointCodec : VestaG → Option (List UInt8))
    (initial rest : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (point : VestaG)
    (entry : TranscriptHashAddress × Fin challengeDigestCard)
    (hentry : entry ∈ (protocolOracleView pointCodec initial digests check (.point point :: rest)).2) :
    HasTranscriptAnchor initial entry.1 point := by
  have hprefix := replayOracleSchedule_queries_prefix
    (protocolOracleReport pointCodec digests check (.point point :: rest)) protocolAttemptContinues
    (protocolQueryAddress initial (.point point :: rest)) digests
    (protocolChallengeCount (.point point :: rest)) 0
  obtain ⟨i, _, hi⟩ := List.mem_map.mp (hprefix.subset hentry)
  rw [← hi]
  exact protocolQueryAddress_anchor initial rest point i

/-- The online oracle tree uses only replies already obtained, filling the rest with zero. -/
def protocolOracleComp (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG))
    (produce : (ℕ → Fin challengeDigestCard) → List (TranscriptElt Fp VestaG))
    (check : (ℕ → Fin challengeDigestCard) → ℕ → Option ProverAttemptFailure) (budget : ℕ) :
    OracleComp TranscriptHashAddress (Fin challengeDigestCard) ProverAttemptResult :=
  prefixOracleComp 0 (fun raw => protocolOracleReport pointCodec raw (check raw) (produce raw))
    protocolAttemptContinues (fun raw => protocolQueryAddress initial (produce raw)) budget []

/-- There is at most one oracle query for each scheduled challenge. -/
theorem protocolOracleComp_queryBound (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG))
    (produce : (ℕ → Fin challengeDigestCard) → List (TranscriptElt Fp VestaG))
    (check : (ℕ → Fin challengeDigestCard) → ℕ → Option ProverAttemptFailure) (budget : ℕ) :
    (protocolOracleComp pointCodec initial produce check budget).QueryBound budget :=
  prefixOracleComp_queryBound _ _ _ _ _ _

/-- Causal messages and checks make online execution equal to replay of the same complete raw tape. -/
theorem protocolOracleComp_replay (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG))
    (produce : (ℕ → Fin challengeDigestCard) → List (TranscriptElt Fp VestaG))
    (check : (ℕ → Fin challengeDigestCard) → ℕ → Option ProverAttemptFailure)
    (hproduce : ProtocolCausal (fun raw i => ((raw i).val : Fp)) produce)
    (hcheck : ProtocolChecksCausal (fun raw i => ((raw i).val : Fp)) check)
    (budget : ℕ) (hcount : ∀ raw, protocolChallengeCount (produce raw) = budget)
    (whole : ℕ → Fin challengeDigestCard) :
    freshOracleRunTape budget (protocolOracleComp pointCodec initial produce check budget) (fun i => whole i.val) =
      some (protocolOracleView pointCodec initial whole (check whole) (produce whole)) := by
  have hreport : ∀ n left right, (∀ i < n, left i = right i) →
      protocolOracleReport pointCodec left (check left) (produce left) n =
        protocolOracleReport pointCodec right (check right) (produce right) n := by
    intro n left right hraw
    exact protocolCausal_observation pointCodec plonkScalarCodec _ check produce hproduce hcheck n left right
      (fun i hi => congrArg (fun digest : Fin challengeDigestCard => (digest.val : Fp)) (hraw i hi))
  have hquery : ∀ n left right, (∀ i < n, left i = right i) →
      protocolQueryAddress initial (produce left) n = protocolQueryAddress initial (produce right) n := by
    intro n left right hraw
    have h := hproduce n left right
      (fun i hi => congrArg (fun digest : Fin challengeDigestCard => (digest.val : Fp)) (hraw i hi))
    simp only [protocolQueryAddress, protocolQueryPrefix, h]
  have h := prefixOracleComp_replay 0
    (fun raw => protocolOracleReport pointCodec raw (check raw) (produce raw)) protocolAttemptContinues
    (fun raw => protocolQueryAddress initial (produce raw)) hreport hquery budget [] whole
    (by intro i hi; simp at hi)
  simpa only [protocolOracleComp, protocolOracleView, hcount, List.length_nil, Nat.zero_add] using h

end Zcash.Snark.ZeroKnowledge
