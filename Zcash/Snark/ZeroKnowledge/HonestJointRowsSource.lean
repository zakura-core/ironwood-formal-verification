import Zcash.Snark.ZeroKnowledge.HonestJointRowsCost
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] rowPolynomial densePolynomial

/-- The complete counted joint view is the original real PLONK and IPA computation on the same material. -/
theorem honestJointRowsCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (constant slope : Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ)
    (sourcePieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hpieces : ∀ i : Fin 8, densePolynomial (pieces.getD i.val []) =
      sourcePieces (rows.map (fun column row => (column row).1)) i) :
    let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 }
    let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
      (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
    let material : PlonkPrivateMaterial actions :=
      (rows.map (fun column row => (column row).1), (constant.1, slope.1), fun i => (entries i).1)
    let data := plonkIpaData urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1 ch.xi.1 ch.z.1
      (fun i => (ch.ipaRound i).1) sourcePieces material
    (honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale generators W U
      instances fixed sigma rows pieces entries ch constant slope tape).1 =
      materializePlonkJointView
        (plonkMaskViewFromMaterial urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x3.1 sourcePieces material,
          ipaTranscriptFromTape data.1 data.2.1 data.2.2 (fun i => (tape i).1)) := by
  let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 }
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  let erows := rows.map (fun column row => (column row).1)
  let blinds := plonkCommitmentBlindsFromVector (fun i => (entries i).1)
  let groups := plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces
    entries ch.x ch.x1 constant slope
  let qb := plonkQuotientPrimeEntry entries
  let data := storedMultiopenDataCosted costs equal read omegaAccess ch.x2 ch.x4 ch.x3 (qb.1, qb.2 + 1) groups.1
  let first := storedFirstOpeningCosted read groups.1
  have hpe : (fun i : Fin 8 => densePolynomial (pieces.getD i.val [])) = sourcePieces erows := funext hpieces
  have hg : groups.1.map StoredOpeningGroup.erase =
      plonkBlindedOpeningGroups pub erows ch.x.1 ch.x1.1 (sourcePieces erows) (constant.1, slope.1) blinds := by
    rewrite [plonkOpeningMaterialCosted_result, hpe]
    rfl
  have hn : ∀ group ∈ groups.1, group.points.length ≤ 4 := by
    intro group hgroup
    have h := plonkOpeningMaterialCosted_points costs equal read omegaAccess instances fixed sigma rows pieces
      entries ch.x ch.x1 constant slope group hgroup
    omega
  have hpoly : (groups.1.map fun group => group.erase.toPolynomialOpeningGroup) =
      plonkPolynomialOpeningGroups pub erows ch.x.1 ch.x1.1 (sourcePieces erows) (constant.1, slope.1) := by
    have h := congrArg (List.map BlindedOpeningGroup.toPolynomialOpeningGroup) hg
    simpa only [List.map_map, Function.comp_def, plonkBlindedOpeningGroups_polynomials] using h
  have hq : densePolynomial data.1.quotientPrime = multiopenQuotientPolynomial ch.x2.1
      (plonkPolynomialOpeningGroups pub erows ch.x.1 ch.x1.1 (sourcePieces erows) (constant.1, slope.1)) := by
    rewrite [storedMultiopenDataCosted_quotient_result costs equal read omegaAccess
      ch.x2 ch.x4 ch.x3 (qb.1, qb.2 + 1) groups.1 hn, hpoly]
    rfl
  have hf : densePolynomial first.1 =
      plonkOpeningPolynomials pub erows ch.x.1 ch.x1.1 (sourcePieces erows) (constant.1, slope.1) 0 := by
    rewrite [storedFirstOpeningCosted_result, hg]
    have h0 : 0 < (plonkBlindedOpeningGroups pub erows ch.x.1 ch.x1.1 (sourcePieces erows)
        (constant.1, slope.1) blinds).length := by simp only [plonkBlindedOpeningGroups, List.length_ofFn]; decide
    rewrite [List.getD_eq_getElem _ _ h0]
    simp only [plonkBlindedOpeningGroups, List.getElem_ofFn, plonkBlindedOpeningGroup]
    rfl
  have hm := honestPlonkMaskCosted_result costs equal read omegaAccess groupAdd groupScale generators W U.1
    rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope pub ch.x1.1 ch.x2.1
    sourcePieces hpieces hq hf
  have hi := preparedHonestIpaCosted_computed costs groupAdd groupScale equal read omegaAccess generators W U
    ch.x2 ch.x4 ch.x3 (qb.1, qb.2 + 1) ch.xi ch.z groups.1 ch.ipaRound tape hn
  rewrite [hg] at hi
  unfold honestJointRowsCosted
  change ((honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
    (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope).1,
    (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data
      ch.x3 ch.xi ch.z ch.ipaRound tape).1) = _
  rewrite [hm, hi]
  rfl

end Zcash.Snark.ZeroKnowledge
