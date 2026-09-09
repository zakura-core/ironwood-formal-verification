import Zcash.Snark.ZeroKnowledge.StoredActionRawStepCost
import Zcash.Snark.ZeroKnowledge.StatefulRetryCost
import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedSource

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey actionRawOracleStep

/-- The actual retry decision reads only the attempt component of the retained observation. -/
def storedActionRecordedRetryCosted (observation : Option ProverAttemptResult × ActionRetryOracleState) : Bool × ℕ :=
  let decision := oracleRetryRequestedCosted observation.1
  (decision.1, decision.2 + 1)

theorem storedActionRecordedRetryCosted_result (observation : Option ProverAttemptResult × ActionRetryOracleState) :
    (storedActionRecordedRetryCosted observation).1 = oracleRetryRequested observation.1 :=
  oracleRetryRequestedCosted_result observation.1

theorem storedActionRecordedRetryCosted_cost_le (observation : Option ProverAttemptResult × ActionRetryOracleState) :
    (storedActionRecordedRetryCosted observation).2 ≤ 6 :=
  Nat.add_le_add_right (oracleRetryRequestedCosted_cost_le observation.1) 1

/-- Run the complete recorded real experiment on stored raw tapes, retaining every intermediate cache. -/
@[irreducible] def storedActionRecordedCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (tapes : List StoredActionRetryTape) (cache : ActionRetryOracleState) : ActionRetryRecordedView × ℕ :=
  let run := runStatefulRetriesCosted
    (storedActionRecordedStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness vkTranscriptRepr) storedActionRecordedRetryCosted tapes cache
  (run.1, run.2 + 1)

/-- Stored representation alone changes: the complete source history, caches, and exhaustion bit are identical. -/
theorem storedActionRecordedCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    {budget : ℕ} (replies : OracleReplyRetryTape 11 budget)
    (privateTape : RawPrivateRetryTape inputs.length budget) (cache : ActionRetryOracleState) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (storedActionRecordedCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr
      (List.ofFn (fun i => (List.ofFn (replies i), List.ofFn (privateTape i)))) cache).1 =
      actionOracleRecordFromRawTapes urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
        replies privateTape cache := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
  let run := storedActionRecordedStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr
  let source := retainRetryState (actionRawOracleStep urs rfl
    (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr)
  let encode := fun tape : ActionRetryRawTape inputs.length 11 => (List.ofFn tape.1, List.ofFn tape.2)
  have hsource : ∀ state tape, (run state (encode tape)).1 = source state tape := by
    intro state tape
    let next := storedActionRawStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr state (encode tape)
    have hs : next.1 = actionRawOracleStep urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
        state tape := storedActionRawStepCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
          inputs generators W U witness vkTranscriptRepr state tape
    unfold run storedActionRecordedStepCosted
    change (next.1, next.1.2) = _
    rewrite [hs]
    rfl
  have hretry : {a | (storedActionRecordedRetryCosted a).1 = true} = retainedStateRetrySet oracleRetrySet := by
    ext observation
    simp only [Set.mem_setOf_eq, storedActionRecordedRetryCosted_result, retainedStateRetrySet, oracleRetrySet]
  have h := runStatefulRetries_map_tape source (fun state tape => (run state tape).1) encode
    (retainedStateRetrySet oracleRetrySet) hsource (List.ofFn (fun i => (replies i, privateTape i))) cache
  simp only [List.map_ofFn, Function.comp_def] at h
  unfold storedActionRecordedCosted
  change (runStatefulRetriesCosted run storedActionRecordedRetryCosted _ cache).1 = _
  rewrite [runStatefulRetriesCosted_result]
  exact (runStatefulRetries_congr_retry _ _ _ hretry _ cache).trans h

end Zcash.Snark.ZeroKnowledge
