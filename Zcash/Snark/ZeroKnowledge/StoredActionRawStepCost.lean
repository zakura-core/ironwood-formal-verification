import Zcash.Snark.ZeroKnowledge.StoredActionCachedRawBound
import Zcash.Snark.ZeroKnowledge.OracleRetryCost
import Zcash.Snark.ZeroKnowledge.ActionOracleStream

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey actionOracleRunTape

/-- Stored raw reply slots and private words for one attempt, in the source experiment's order. -/
abbrev StoredActionRetryTape := List (Fin challengeDigestCard) × List (Fin challengeDigestCard)

/-- The complete counted real attempt, returning precisely the state consumed by the next retry. -/
@[irreducible] def storedActionRawStepCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : StoredActionRetryTape) :
    (Option ProverAttemptResult × ActionRetryOracleState) × ℕ :=
  let run := storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness vkTranscriptRepr cache tape.2 tape.1
  let state := oracleAttemptStateCosted cache run.1
  (state.1, run.2 + state.2 + 2)

/-- Every returned cache is retained as an observation as well as passed to the next attempt. -/
@[irreducible] def storedActionRecordedStepCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : StoredActionRetryTape) :
    ((Option ProverAttemptResult × ActionRetryOracleState) × ActionRetryOracleState) × ℕ :=
  let step := storedActionRawStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness vkTranscriptRepr cache tape
  ((step.1, step.1.2), step.2 + 3)

/-- Erasing the counter recovers the actual raw Action transition, including every failure case. -/
theorem storedActionRawStepCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : ActionRetryRawTape inputs.length 11) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (storedActionRawStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr cache
      (List.ofFn tape.1, List.ofFn tape.2)).1 =
      actionRawOracleStep urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr cache tape := by
  dsimp only
  unfold storedActionRawStepCosted
  rewrite [oracleAttemptStateCosted_result, storedActionCachedRawCosted_result]
  rfl

/-- The state adapter preserves the established twenty-two-entry bound even when the attempt is absent. -/
theorem storedActionRawStepCosted_cache_length_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : StoredActionRetryTape) :
    (storedActionRawStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness vkTranscriptRepr cache tape).1.2.length ≤ cache.length + 22 := by
  let run := storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness vkTranscriptRepr cache tape.2 tape.1
  have h : ∀ result finalCache, (result, finalCache) ∈ run.1 → finalCache.length ≤ cache.length + 22 :=
    storedActionCachedRawCosted_cache_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness vkTranscriptRepr cache tape.2 tape.1
  unfold storedActionRawStepCosted
  change (oracleAttemptStateCosted cache run.1).1.2.length ≤ _
  cases hr : run.1 with
  | none => exact Nat.le_add_right _ _
  | some pair =>
    rcases pair with ⟨result, finalCache⟩
    exact h result finalCache (by rewrite [hr]; exact Option.mem_def.mpr rfl)

end Zcash.Snark.ZeroKnowledge
