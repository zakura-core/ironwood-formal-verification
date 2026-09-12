import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBitsLaw

/-!
# Stored inputs and primitive prices for executable PRNG reductions

Execution consumes only materialized data. `ofReference` is the representation
map in refinement theorems: it identifies the stored key, setup, and witness
with the original mathematical inputs. It is not a free preprocessing callback
invoked by the reduction. Witness and key generation remain outside this
stored-input execution model; all reads of those inputs are already charged.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- Prices of the explicitly modeled primitives, shared by all components of the reduction. -/
structure ActionReductionPrices where
  field : FieldOperationCosts
  node : ℕ
  equal : ℕ
  read : ℕ
  omegaAccess : ℕ
  canonicalRead : ℕ
  compare : ℕ
  groupAdd : ℕ
  groupScale : ℕ

/-- All fixed inputs consumed by the stored real prover and its distinguishing test. -/
structure ActionReductionData where
  inputs : List (PublicInputs Fp)
  setup : StoredPlonkSetup VestaG
  key : StoredPlonkKey
  witnessRows : List (List (List Fp))
  vkTranscriptRepr : Fp
  cache : ActionRetryOracleState
  auxiliary : List (Fin challengeDigestCard)

/-- Reference inputs represented as stored data, with the actual Action compiler and original witness rows. -/
def ActionReductionData.ofReference (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard)) : ActionReductionData :=
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
  ⟨inputs, setup, StoredPlonkKey.encode vk, encodeActionWitness witness, vkTranscriptRepr, cache, auxiliary⟩

/-- Only input representation and shape are certified here; no prover result or running-time bound is assumed. -/
def ActionReductionData.WellFormed (data : ActionReductionData) : Prop :=
  ∃ (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin data.inputs.length → Fin 10 → Fin 2048 → Fp),
    data.setup = StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit) ∧
    data.key = StoredPlonkKey.encode (actionReferenceKey (actions := data.inputs.length)
      ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl actionCircuit_newFixedCols_eq_fifteen) ∧
    data.witnessRows = encodeActionWitness witness

/-- Every source input supplies the structural certificate, including invalid witnesses and exceptional values. -/
theorem ActionReductionData.ofReference_wellFormed (inputs : List (PublicInputs Fp))
    (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard)) :
    (ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary).WellFormed :=
  ⟨generators, W, U, witness, rfl, rfl, rfl⟩

end Zcash.Snark.ZeroKnowledge
