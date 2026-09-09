import Zcash.Snark.ZeroKnowledge.StoredActionCachedFieldsBound
import Zcash.Snark.ZeroKnowledge.StoredRawFieldCost
import Zcash.Snark.ZeroKnowledge.StoredActionInitialCost
import Zcash.Snark.ZeroKnowledge.ActionGateDegree
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate
import Zcash.Snark.ZeroKnowledge.ActionOracleRetrySource

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey plonkReferenceOracleComp cachedOracleRunTape
  plonkPublicPolynomialsFromRows storedRawFieldsCosted storedActionInitialCosted

/-- Execute the complete actual cached Action attempt from its stored raw private and oracle tapes. -/
@[irreducible] def storedActionCachedRawCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (privateWords replies : List (Fin challengeDigestCard)) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) × ℕ :=
  let fields := storedRawFieldsCosted (fieldSampleCount inputs.length) read privateWords
  let initial := storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs setup (vkTranscriptRepr, read + 1)
  let run := storedActionCachedFieldsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness fields.1 initial.1 cache replies
  (run.1, fields.2 + initial.2 + run.2 + 3)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- The actual Action compiler discharges all source conditions of the complete raw cached implementation. -/
theorem storedActionCachedRawCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (privateWords : RawPrivateTape inputs.length) (replies : Fin 22 → Fin challengeDigestCard) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG :=
      actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr cache
      (List.ofFn privateWords) (List.ofFn replies)).1 =
      actionOracleRunTape urs rfl (fun index : Fin inputs.length => inputs[index.val]) witness vkTranscriptRepr cache
        (actionRawOracleTape (replies, privateWords)) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let setup := StoredPlonkSetup.encode generators W U
    (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
  let packed := actionCircuit_newFixedCols_eq_fifteen
  let vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG := actionReferenceKey (actions := inputs.length) urs rfl packed
  let fields := storedRawFieldsCosted (fieldSampleCount inputs.length) read (List.ofFn privateWords)
  let initial := storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs setup (vkTranscriptRepr, read + 1)
  have hf : fields.1 = List.ofFn (reduceFieldTape privateWords) :=
    storedRawFieldsCosted_ofFn_result (fieldSampleCount inputs.length) read privateWords
  have hi : initial.1 = actionOracleInitial urs vkTranscriptRepr (fun index : Fin inputs.length => inputs[index.val]) :=
    storedActionInitialCosted_result costs groupAdd groupScale read omegaAccess inputs generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit) (vkTranscriptRepr, read + 1)
  have hd := actionReferenceKey_domain (actions := inputs.length) urs rfl packed
  have h := storedActionCachedFieldsCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit) vk witness
    (reduceFieldTape privateWords) (actionOracleInitial urs vkTranscriptRepr (fun index : Fin inputs.length => inputs[index.val]))
    cache replies (actionReferenceKey_degreeProfile (actions := inputs.length) urs rfl packed) hd.1 hd.2
    (actionReferenceKey_queryLayout (actions := inputs.length) urs rfl packed).blinding
  unfold storedActionCachedRawCosted
  change (storedActionCachedFieldsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) fields.1 initial.1 cache (List.ofFn replies)).1 = _
  rewrite [hf, hi]
  unfold actionOracleRunTape actionOracleComp actionRawOracleTape actionPublicPolynomials plonkKeygenPublicPolynomials
  exact h

end Zcash.Snark.ZeroKnowledge
