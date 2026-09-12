import Zcash.Snark.ZeroKnowledge.PlonkMaskSimulatorCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkKeyCost
import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningCost
import Zcash.Snark.ZeroKnowledge.IpaPreparedInputCost
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost

/-!
# Counted complete joint PLONK and IPA simulation

The algorithm materializes the PLONK mask, constructs readers for those stored
entries, computes the complete inferred quotient and public opening, and runs the
fully materialized IPA simulator. Each preparation cost is retained explicitly.
There is no supplied quotient callback whose computation is left unpriced.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Materialize both parts of the original joint simulator's finite observation. -/
def materializePlonkJointView {actions k : ℕ}
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G :=
  (materializePlonkMaskView view.1, materializedIpaTranscript view.2)

/-- Compute every joint-simulator field, including the original quotient and opening. -/
def plonkJointSimulatorCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ) (key : StoredPlonkKey)
    (ch : Challenges 11 (Fp × ℕ)) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  let mask := materializedPlonkMaskSimulatorCosted ipaCosts.groupScale W blinds observations linear firstGroup
  let views := storedRowReadersCosted read (0 : Fp) 5 mask.1.2.1
  let points := fun index : Fin (22 * actions + 10) => getDListCosted read (0 : G) mask.1.1 index.val
  let hx := plonkVerifierHxCosted fieldCosts node equal read omegaAccess instances fixed sigma views.1
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    (key.omega, read + 1) key.n key.blindingFactors ch.beta ch.gamma ch.x ch.y
    (key.delta, read + 1) ch.theta key.chunkLen
  let opening := plonkPublicOpeningCosted fieldCosts ipaCosts.groupAdd ipaCosts.groupScale equal read omegaAccess
    instances fixed sigma generators W points views.1 ch.x ch.x1 ch.x2 ch.x4 ch.x3
    (hx.1, 1) (mask.1.2.2.1, 1) (mask.1.2.2.2, 1)
  let ipa := preparedIpaSimulatorCosted ipaCosts generators W U opening ch.x3 ch.xi ch.z ch.ipaRound
    roundCoins scalarCoin finalBlind
  ((mask.1, ipa.1), mask.2 + views.2 + hx.2 + ipa.2 + 3 * (read + 1) + 4)

set_option maxRecDepth 5000 in
/-- Erasure gives the complete original joint simulator, with the verifier quotient computed internally. -/
theorem plonkJointSimulatorCosted_result (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (vk : VerifyingKey (plonkProofShape actions 11) Fp G)
    (ch : Challenges 11 (Fp × ℕ)) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ) :
    let urs : URS G := { k := 11, g := fun index => (generators index).1, w := W.1, u := U.1 }
    let pub := plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
      (fun column row => (fixed column row).1) (fun column row => (sigma column row).1)
    (plonkJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess instances fixed sigma
      generators W U (StoredPlonkKey.encode vk) ch blinds observations linear firstGroup
      roundCoins scalarCoin finalBlind).1 =
      materializePlonkJointView (plonkJointSimulatorFromCoins urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1
        ch.xi.1 ch.z.1 (fun index => (ch.ipaRound index).1) (plonkVerifierHx vk pub (Challenges.eraseCosts ch))
        (fun index => (blinds index).1, fun column index => (observations column index).1, linear.1, firstGroup.1)
        (fun index => (roundCoins index).1) scalarCoin.1 finalBlind.1) := by
  let urs : URS G := { k := 11, g := fun index => (generators index).1, w := W.1, u := U.1 }
  let pub := plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
    (fun column row => (fixed column row).1) (fun column row => (sigma column row).1)
  let key := StoredPlonkKey.encode vk
  let view := plonkMaskSimulatorFromCoins W.1
    (fun index => (blinds index).1, fun column index => (observations column index).1, linear.1, firstGroup.1)
  let mask := materializedPlonkMaskSimulatorCosted ipaCosts.groupScale W blinds observations linear firstGroup
  let views := storedRowReadersCosted read (0 : Fp) 5 mask.1.2.1
  let points := fun index : Fin (22 * actions + 10) => getDListCosted read (0 : G) mask.1.1 index.val
  let hx := plonkVerifierHxCosted fieldCosts node equal read omegaAccess instances fixed sigma views.1
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    (key.omega, read + 1) key.n key.blindingFactors ch.beta ch.gamma ch.x ch.y
    (key.delta, read + 1) ch.theta key.chunkLen
  let opening := plonkPublicOpeningCosted fieldCosts ipaCosts.groupAdd ipaCosts.groupScale equal read omegaAccess
    instances fixed sigma generators W points views.1 ch.x ch.x1 ch.x2 ch.x4 ch.x3
    (hx.1, 1) (mask.1.2.2.1, 1) (mask.1.2.2.2, 1)
  have hmask : mask.1 = materializePlonkMaskView view :=
    materializedPlonkMaskSimulatorCosted_result _ _ _ _ _ _
  have hpoints (index : Fin (22 * actions + 10)) : (points index).1 = view.1 index := by
    dsimp only [points]
    rw [hmask]
    exact getDListCosted_ofFn_result read 0 view.1 index
  have hviews : views.1.map (fun column index => (column index).1) = view.2.1 := by
    dsimp only [views]
    rw [hmask]
    exact storedRowReadersCosted_erase_materialize read 0 view.2.1
  have hview : ((fun index => (points index).1), views.1.map (fun column index => (column index).1),
      mask.1.2.2.1, mask.1.2.2.2) = view := by
    rw [show (fun index => (points index).1) = view.1 from funext hpoints, hviews]
    rfl
  have hinputs : key.lookupInputCosted read = fun index =>
      (vk.lookupInputExprs index, (key.lookupInputCosted read index).2) := by
    funext index
    exact Prod.ext (StoredPlonkKey.lookupInputCosted_encode_result vk read index) rfl
  have htables : key.lookupTableCosted read = fun index =>
      (vk.lookupTableExprs index, (key.lookupTableCosted read index).2) := by
    funext index
    exact Prod.ext (StoredPlonkKey.lookupTableCosted_encode_result vk read index) rfl
  have hhx : hx.1 = plonkVerifierHx vk pub (Challenges.eraseCosts ch) (privateColumnView view.2.1) := by
    dsimp only [hx]
    rw [hinputs, htables]
    have h := plonkVerifierHxCosted_result fieldCosts node equal read omegaAccess vk instances fixed sigma views.1
      (read + 1) (read + 1) (fun index => (key.lookupInputCosted read index).2)
      (fun index => (key.lookupTableCosted read index).2) (Challenges.eraseCosts ch)
      (read + 1) ch.beta.2 ch.gamma.2 ch.x.2 ch.y.2 (read + 1) ch.theta.2
    rw [hviews] at h
    exact h
  have hopening : opening.1 =
      let original := plonkPublicOpening urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1
        (plonkVerifierHx vk pub (Challenges.eraseCosts ch) (privateColumnView view.2.1)) view
      (original.1.eval urs, original.2) := by
    have h := plonkPublicOpeningCosted_result fieldCosts ipaCosts.groupAdd ipaCosts.groupScale equal read omegaAccess
      instances fixed sigma generators W U.1 points views.1 ch.x ch.x1 ch.x2 ch.x4 ch.x3
      (hx.1, 1) (mask.1.2.2.1, 1) (mask.1.2.2.2, 1)
    dsimp only at h
    change opening.1 = _ at h
    rw [hview, hhx] at h
    exact h
  have hinput : (prepareIpaPublicCosted generators W U opening ch.x3 ch.xi ch.z ch.ipaRound).1.erase =
      plonkPublicIpaInput urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1
        (fun index => (ch.ipaRound index).1) (plonkVerifierHx vk pub (Challenges.eraseCosts ch)) view := by
    rw [prepareIpaPublicCosted_result, hopening]
    rfl
  change (mask.1, (preparedIpaSimulatorCosted ipaCosts generators W U opening ch.x3 ch.xi ch.z ch.ipaRound
    roundCoins scalarCoin finalBlind).1) = _
  rw [hmask, preparedIpaSimulatorCosted_result, hinput]
  rfl

end Zcash.Snark.ZeroKnowledge
