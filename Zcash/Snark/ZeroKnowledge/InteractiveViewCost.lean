import Zcash.Snark.ZeroKnowledge.ActionReductionData
import Zcash.Snark.ZeroKnowledge.CanonicalObserverCost
import Zcash.Snark.ZeroKnowledge.ActionRandomnessSource

/-!
# A stored representation of the complete interactive verifier view

The first frame is the original observed attempt. The second frame stores all
22 verifier challenges, including those unused after an early failure. Empty
caches and a false exhaustion flag are fixed representation metadata. This is
an encoding for the existing indexed test language, not a retry experiment.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey plonkReferenceProofFromTape
  plonkPublicPolynomialsFromRows plonkAttemptTrace

/-- Store the original attempt and complete verifier sequence in two public frames. -/
def interactiveViewFrames (sequence : List Fp) (attempt : ProverAttemptResult) : ActionRetryRecordedView :=
  (⟨[(some attempt, []), (some ⟨[], sequence, .complete⟩, [])], false⟩, [])

/-- Encode the full original interactive view for the same concrete indexed tests. -/
def interactiveRecordedView (view : Challenges 11 Fp × ProverAttemptResult) : ActionRetryRecordedView :=
  interactiveViewFrames (plonkChallengeSequence view.1) view.2

/-- Recompute the original real proof, observe it, and explicitly materialize all verifier challenges. -/
@[irreducible] def interactiveHistoryViewCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (privateFields : List Fp) (history : List (Fin challengeDigestCard)) : ActionRetryRecordedView × ℕ :=
  let produced := storedActionHistoryTraceCosted prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows
    privateFields history
  let observed := canonicalProtocolObserverCosted prices.equal prices.read produced.1.1 produced.1.2
  let sequence := plonkChallengeSequenceCosted produced.1.1
  (interactiveViewFrames sequence.1 observed.1, produced.2 + observed.2 + sequence.2 + 14)

set_option maxRecDepth 10000 in
/-- Erasure is the complete original interactive Action computation for every challenge and private tape. -/
theorem interactiveHistoryViewCosted_result (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (privateFields : Fin (fieldSampleCount inputs.length) → Fp) (history : List (Fin challengeDigestCard)) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (interactiveHistoryViewCosted prices
      (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      (List.ofFn privateFields) history).1 =
      interactiveRecordedView (plonkReferenceAttemptFromTape urs rfl vk
        (actionPublicPolynomials (fun i : Fin inputs.length => inputs[i.val])) witness
        (plonkChallengesFromDigests 11 (oracleHistoryTape 0 history)) privateFields) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let packed := actionCircuit_newFixedCols_eq_fifteen
  let vk := actionReferenceKey (actions := inputs.length) urs rfl packed
  let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
  let produced := storedActionHistoryTraceCosted prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows
    (List.ofFn privateFields) history
  have hch : Challenges.eraseCosts produced.1.1 = plonkChallengesFromDigests 11 (oracleHistoryTape 0 history) := by
    unfold produced storedActionHistoryTraceCosted
    exact storedHistoryChallengesCosted_result prices.read history
  have hd := actionReferenceKey_domain (actions := inputs.length) urs rfl packed
  have ht := storedActionHistoryTraceCosted_result prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale inputs generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit) vk witness privateFields history
    (actionReferenceKey_degreeProfile (actions := inputs.length) urs rfl packed) hd.1 hd.2
    (actionReferenceKey_queryLayout (actions := inputs.length) urs rfl packed).blinding
  unfold interactiveHistoryViewCosted
  change interactiveViewFrames (plonkChallengeSequenceCosted produced.1.1).1
    (canonicalProtocolObserverCosted prices.equal prices.read produced.1.1 produced.1.2).1 = _
  rewrite [plonkChallengeSequenceCosted_result, canonicalProtocolObserverCosted_result, hch]
  have htrace : produced.1.2 = _ := ht
  rewrite [htrace]
  dsimp only [interactiveRecordedView, plonkReferenceAttemptFromTape, encodedPlonkAttempt,
    plonkAttemptObservation, observePlonkAttempt, actionPublicPolynomials, plonkKeygenPublicPolynomials]

end Zcash.Snark.ZeroKnowledge
