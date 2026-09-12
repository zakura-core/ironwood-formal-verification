import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialCost
import Zcash.Snark.ZeroKnowledge.StoredPrivateMaterialSource

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp omegaOf URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] plonkStoredMaterialFromTapeCosted rowPolynomial densePolynomial

/-- The complete stored prover recovers the original private material and computed quotient before the real IPA. -/
theorem honestStoredMaterialCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (vk : VerifyingKey (plonkProofShape actions 11) Fp G)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (preIpa : Fin (batchedColumnSampleCount (plonkColumnBatches (plonkTotalColumnConstructor vk
      (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
      (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch))) + 12) → Fp)
    (ipaTape : Fin (ipaSampleCount 11) → Fp × ℕ) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 }
    let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
      (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
    let construct := plonkTotalColumnConstructor vk pub (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch)
    let material := plonkMaterialFromTape construct [] preIpa
    let pieces := fun rows => plonkQuotientPieces (plonkConstraintNumerator vk pub (Challenges.eraseCosts ch) rows)
    let data := plonkIpaData urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1
      (fun i => (ch.ipaRound i).1) pieces material
    (honestStoredMaterialCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      (StoredPlonkKey.encode vk) generators W U instances fixed sigma witness ch (List.ofFn preIpa) ipaTape).1 =
      materializePlonkJointView
        (plonkMaskViewFromMaterial urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x3.1 pieces material,
          ipaTranscriptFromTape data.1 data.2.1 data.2.2 (fun i => (ipaTape i).1)) := by
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  let source := plonkTotalColumnConstructor vk pub (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch)
  let material := plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare
    (StoredPlonkKey.encode vk) instances fixed sigma witness ch.theta ch.beta ch.gamma (List.ofFn preIpa)
  let rows := storedRowReadersCosted read (0 : Fp) 2048 material.1.1
  let pieces := plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk)
    ch instances fixed sigma rows.1
  let entries := fun i : Fin (22 * actions + 10) => getDListCosted read (0 : Fp) material.1.2.2 i.val
  let sourcePieces := fun values => plonkQuotientPieces (plonkConstraintNumerator vk pub (Challenges.eraseCosts ch) values)
  have hmaterial : material.1 =
      ((plonkMaterialFromTape source [] preIpa).1.map List.ofFn,
        (plonkMaterialFromTape source [] preIpa).2.1, List.ofFn (plonkMaterialFromTape source [] preIpa).2.2) :=
    plonkStoredMaterialFromTapeCosted_result costs node equal read omegaAccess canonicalRead compare vk
      instances fixed sigma witness (Challenges.eraseCosts ch) ch.theta.2 ch.beta.2 ch.gamma.2 preIpa
  have hdecoded : ((rows.1.map (fun column row => (column row).1)), material.1.2.1,
      (fun i => (entries i).1)) = plonkMaterialFromTape source [] preIpa := by
    rewrite [storedPrivateMaterial_readers, hmaterial, storedPrivateMaterial_materialize]
    rfl
  have hp := plonkQuotientPiecesFromRowsCosted_result costs node equal read omegaAccess vk ch
    instances fixed sigma rows.1 profile homega hn hblind
  have hpieces (i : Fin 8) : densePolynomial (pieces.1.getD i.val []) =
      sourcePieces (rows.1.map (fun column row => (column row).1)) i := by
    change pieces.1.map densePolynomial = List.ofFn (sourcePieces (rows.1.map (fun column row => (column row).1))) at hp
    rewrite [densePolynomial_getD, hp,
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
    rfl
  have hj := honestJointRowsCosted_result costs equal read omegaAccess groupAdd groupScale generators W U
    instances fixed sigma rows.1 pieces.1 entries ch (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2)
    ipaTape sourcePieces hpieces
  change (honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale generators W U
    instances fixed sigma rows.1 pieces.1 entries ch (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2)
    ipaTape).1 = _ at hj
  rewrite [hdecoded] at hj
  unfold honestStoredMaterialCosted
  exact hj

end Zcash.Snark.ZeroKnowledge
