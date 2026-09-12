import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBits

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- The counted real retry implementation has exactly the original reduction's verifier-coin law.
This equality holds for each entire private prefix, including arbitrarily correlated candidate words. -/
theorem storedActionRecordedBitsCosted_law (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (privateTape : RawPrivateRetryTape inputs.length budget) (cache : ActionRetryOracleState) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (PMF.uniformOfFintype (Fin ((budget * 22) * 512) → Bool)).map (fun bits =>
      (storedActionRecordedBitsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr budget
        (List.ofFn bits) (List.ofFn (fun i => List.ofFn (privateTape i))) cache).1) =
      (PMF.uniformOfFintype (OracleReplyRetryTape 11 budget)).map (fun replies =>
        actionOracleRecordFromRawTapes urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
          replies privateTape cache) := by
  dsimp only
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  have h := congrArg (PMF.map (fun replies : OracleReplyRetryTape 11 budget =>
    actionOracleRecordFromRawTapes urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
      replies privateTape cache)) (uniformRawMatrixBits budget 22)
  simp only [PMF.map_comp, Function.comp_def] at h
  simp only [storedActionRecordedBitsCosted_result]
  exact h

end Zcash.Snark.ZeroKnowledge
