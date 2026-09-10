import Zcash.Snark.ZeroKnowledge.HonestTapeJointBound
import Zcash.Snark.ZeroKnowledge.StoredActionWitnessCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkSetupCost
import Zcash.Snark.ZeroKnowledge.ActionPublicInputCost
import Zcash.Snark.ZeroKnowledge.PlonkCausality

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp omegaOf URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] rowPolynomial plonkJointSampleCount plonkPublicPolynomialsFromRows
  plonkTotalColumnConstructor plonkJointViewFromTape plonkHonestQuotientPieces

/-- The actual real prover with stored Action inputs, setup, and advice witness. -/
@[irreducible] def storedActionHonestJointCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (ch : Challenges 11 (Fp × ℕ)) (tape : List Fp) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  honestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale key
    (setup.generatorCosted read) (setup.w, read + 1) (setup.u, read + 1)
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (fun action => storedActionWitnessRowCosted read witness action.val) ch tape

set_option maxRecDepth 10000 in
/-- The stored implementation preserves the complete original Action reference joint view and its tape cast. -/
theorem storedActionHonestJointCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 (Fp × ℕ)) (tape : Fin (fieldSampleCount inputs.length) → Fp)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    let construct := plonkTotalColumnConstructor vk pub witness (Challenges.eraseCosts ch)
    (storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) ch (List.ofFn tape)).1 =
      materializePlonkJointView (plonkJointViewFromTape construct [] urs pub
        ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1 (fun i => (ch.ipaRound i).1)
        (plonkHonestQuotientPieces vk pub (Challenges.eraseCosts ch))
        (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl))) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let instanceRows := actionStoredInstanceRowCosted read inputs
  let advice := fun action : Fin inputs.length => storedActionWitnessRowCosted read (encodeActionWitness witness) action.val
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instanceRows a r).1)
    (fun c r => (setup.fixedCosted read c r).1) (fun c r => (setup.sigmaCosted read c r).1)
  let construct := plonkTotalColumnConstructor vk pub (fun a c r => (advice a c r).1) (Challenges.eraseCosts ch)
  have hcast : List.ofFn (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl)) = List.ofFn tape := by
    exact (List.ofFn_congr (plonkJointSampleCount_eq construct rfl).symm tape).symm
  have hi : (fun a r => (instanceRows a r).1) =
      actionInstanceRows (fun action : Fin inputs.length => inputs[action.val]) := by
    funext a r
    exact actionStoredInstanceRowCosted_result read inputs a r
  have hf : (fun c r => (setup.fixedCosted read c r).1) = fixed := by
    funext c r
    exact StoredPlonkSetup.fixedCosted_encode_result generators W U fixed sigma read c r
  have hs : (fun c r => (setup.sigmaCosted read c r).1) = sigma := by
    funext c r
    exact StoredPlonkSetup.sigmaCosted_encode_result generators W U fixed sigma read c r
  have hg : (fun i : Fin (2 ^ 11) => (setup.generatorCosted read i).1) = generators := by
    funext i
    exact StoredPlonkSetup.generatorCosted_encode_result generators W U fixed sigma read i
  have hw : (fun a c r => (advice a c r).1) = witness := by
    funext a c r
    exact storedActionWitnessRowCosted_result read witness a c r
  have h := honestTapeJointCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    vk (setup.generatorCosted read) (W, read + 1) (U, read + 1) instanceRows (setup.fixedCosted read)
    (setup.sigmaCosted read) advice ch (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl))
    profile homega hn hblind
  rewrite [hcast] at h
  change (honestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    (StoredPlonkKey.encode vk) (setup.generatorCosted read) (W, read + 1) (U, read + 1)
    instanceRows (setup.fixedCosted read) (setup.sigmaCosted read) advice ch (List.ofFn tape)).1 =
    materializePlonkJointView (plonkJointViewFromTape construct []
      ({ k := 11, g := fun i => (setup.generatorCosted read i).1, w := W, u := U } : URS G) pub
      ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1 (fun i => (ch.ipaRound i).1)
      (fun rows => plonkQuotientPieces (plonkConstraintNumerator vk pub (Challenges.eraseCosts ch) rows))
      (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl))) at h
  conv at h => rhs; unfold construct pub; rewrite [hi, hf, hs, hg, hw]
  unfold storedActionHonestJointCosted plonkHonestQuotientPieces
  exact h

end Zcash.Snark.ZeroKnowledge
