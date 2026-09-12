import Zcash.Snark.ZeroKnowledge.ActionReductionData
import Zcash.Snark.ZeroKnowledge.RecordedTestProgram

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- Run the actual prover, retain the auxiliary cells, and execute a concrete public-view test circuit. -/
@[irreducible] def observedReductionCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (budget : ℕ) (bits : List Bool)
    (privateRows : List (List (Fin challengeDigestCard))) : Bool × ℕ :=
  let auxiliary := copyAuxiliaryWordsCosted prices.read data.auxiliary
  let produced := storedActionRecordedBitsCosted prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows
    data.vkTranscriptRepr budget bits privateRows data.cache
  let tested := recordedViewTestCosted program prices.read prices.canonicalRead auxiliary.1 produced.1
  (tested.1, auxiliary.2 + produced.2 + tested.2 + 3)

/-- The whole reduction budget includes all auxiliary input materialization, real retries, and test instructions. -/
def observedReductionCostBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (budget bitLength : ℕ) : ℕ :=
  data.auxiliary.length * (prices.read + 2) + 1 +
    storedActionRecordedBitsCostBudget prices.field prices.node prices.equal prices.read prices.omegaAccess
      prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs.length budget data.cache.length bitLength data.key +
    recordedViewTestCostBudget program prices.read prices.canonicalRead + 3

/-- The complete real-prover-and-test reduction has a checked bound, with no whole-prover runtime premise. -/
theorem observedReductionCosted_cost_le (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (program : RecordedTestProgram) (budget : ℕ) (bits : List Bool)
    (privateRows : List (List (Fin challengeDigestCard))) (hlength : privateRows.length = budget)
    (hwidth : ∀ row ∈ privateRows, row.length = fieldSampleCount data.inputs.length) :
    (observedReductionCosted prices data program budget bits privateRows).2 ≤
      observedReductionCostBudget prices data program budget bits.length := by
  let produced := storedActionRecordedBitsCosted prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows
    data.vkTranscriptRepr budget bits privateRows data.cache
  have hp : produced.2 ≤ storedActionRecordedBitsCostBudget prices.field prices.node prices.equal prices.read prices.omegaAccess
      prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs.length budget data.cache.length bits.length data.key := by
    obtain ⟨generators, W, U, witness, hs, hk, hw⟩ := hdata
    unfold produced
    rewrite [hs, hk, hw]
    exact storedActionRecordedBitsCosted_cost_le prices.field prices.node prices.equal prices.read prices.omegaAccess
      prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
      (actionReferenceKey (actions := data.inputs.length) ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
        rfl actionCircuit_newFixedCols_eq_fifteen) witness data.vkTranscriptRepr budget bits privateRows data.cache hlength hwidth
  have ha := copyAuxiliaryWordsCosted_cost_le prices.read data.auxiliary
  have ht := recordedViewTestCosted_cost_le program prices.read prices.canonicalRead
    (copyAuxiliaryWordsCosted prices.read data.auxiliary).1 produced.1
  unfold observedReductionCosted observedReductionCostBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ha hp) ht) 3

/-- The counted test sees precisely the original complete recorded Action execution. -/
theorem observedReductionCosted_result (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget : ℕ) (bits : Fin ((budget * 22) * 512) → Bool)
    (privateTape : RawPrivateRetryTape inputs.length budget) :
    (observedReductionCosted prices (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      program budget (List.ofFn bits) (List.ofFn (fun i => List.ofFn (privateTape i)))).1 =
      recordedViewTest program auxiliary
        (actionOracleRecordFromRawTapes ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
          rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr (rawMatrixBitsEquiv budget 22 bits) privateTape cache) := by
  unfold observedReductionCosted
  dsimp only [ActionReductionData.ofReference]
  rewrite [recordedViewTestCosted_result, copyAuxiliaryWordsCosted_result, storedActionRecordedBitsCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
