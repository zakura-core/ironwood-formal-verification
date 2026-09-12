import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialSource
import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp omegaOf URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Split the original complete private tape, then construct and materialize the entire real joint view. -/
@[irreducible] def honestTapeJointCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (tape : List Fp) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  let parts := splitListCosted read (148 * actions + 12) tape
  let joint := honestStoredMaterialCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    key generators W U instances fixed sigma witness ch parts.1.1
    (fun i => getDListCosted read (0 : Fp) parts.1.2 i.val)
  (joint.1, parts.2 + joint.2 + 2)

/-- The complete counted execution is the original tape-driven joint prover, without a challenge exclusion. -/
theorem honestTapeJointCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (vk : VerifyingKey (plonkProofShape actions 11) Fp G)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk
      (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
      (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch)) 11) → Fp)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 }
    let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
      (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
    let construct := plonkTotalColumnConstructor vk pub (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch)
    (honestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      (StoredPlonkKey.encode vk) generators W U instances fixed sigma witness ch (List.ofFn tape)).1 =
      materializePlonkJointView (plonkJointViewFromTape construct [] urs pub
        ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1 (fun i => (ch.ipaRound i).1)
        (fun rows => plonkQuotientPieces (plonkConstraintNumerator vk pub (Challenges.eraseCosts ch) rows)) tape) := by
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  let construct := plonkTotalColumnConstructor vk pub (fun a c r => (witness a c r).1) (Challenges.eraseCosts ch)
  let parts := splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12) (ipaSampleCount 11) Fp tape
  have hc : batchedColumnSampleCount (plonkColumnBatches construct) + 12 = 148 * actions + 12 := by
    rewrite [plonkColumnBatches_sample_count]
    rfl
  have hl : (splitListCosted read (148 * actions + 12) (List.ofFn tape)).1.1 = List.ofFn parts.1 := by
    rewrite [splitListCosted_result]
    rewrite [← hc]
    exact (ofFn_splitTape_left Fp _ _ tape).symm
  have hr : (splitListCosted read (148 * actions + 12) (List.ofFn tape)).1.2 = List.ofFn parts.2 := by
    rewrite [splitListCosted_result]
    rewrite [← hc]
    exact (ofFn_splitTape_right Fp _ _ tape).symm
  unfold honestTapeJointCosted
  change (honestStoredMaterialCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    (StoredPlonkKey.encode vk) generators W U instances fixed sigma witness ch
    (splitListCosted read (148 * actions + 12) (List.ofFn tape)).1.1
    (fun i => getDListCosted read (0 : Fp) (splitListCosted read (148 * actions + 12) (List.ofFn tape)).1.2 i.val)).1 = _
  rewrite [hl, hr, honestStoredMaterialCosted_result costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale vk generators W U instances fixed sigma witness ch parts.1 _ profile homega hn hblind]
  simp only [getDListCosted_ofFn_result]
  rfl

end Zcash.Snark.ZeroKnowledge
