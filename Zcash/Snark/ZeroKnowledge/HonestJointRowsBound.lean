import Zcash.Snark.ZeroKnowledge.HonestJointRowsCost
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Full real joint-prover budget, retaining the actual scalar-access prices. -/
def honestJointRowsCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale actions rows pieces rowRead access tapeAccess : ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (constantRead slopeRead : ℕ) : ℕ :=
  plonkOpeningMaterialCostBudget costs equal read omegaAccess actions rows pieces
    rowRead access ch.x.2 ch.x1.2 constantRead slopeRead +
  honestPlonkMaskCostBudget costs equal read omegaAccess groupAdd groupScale actions rows pieces
    rowRead access access ch.x.2 ch.x3.2 constantRead slopeRead (read + 1) (read + 12) access +
  preparedHonestIpaCostBudget costs groupAdd groupScale equal read
    (storedMultiopenDataCostBudget costs equal read omegaAccess ch.x2.2 ch.x4.2 ch.x3.2 (access + 1))
    access tapeAccess + 1

/-- Actual row, coefficient, and tape dimensions discharge the complete joint real-prover cost. -/
theorem honestJointRowsCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (constant slope : Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ)
    (rowRead access tapeAccess : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead)
    (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048)
    (hentries : ∀ i, (entries i).2 ≤ access) (hg : ∀ i, (generators i).2 ≤ access)
    (hW : W.2 ≤ access) (hU : U.2 ≤ access) (hch : Challenges.ReadBound ch access)
    (htape : ∀ i, (tape i).2 ≤ tapeAccess) :
    (honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale generators W U
      instances fixed sigma rows pieces entries ch constant slope tape).2 ≤
      honestJointRowsCostBudget costs equal read omegaAccess groupAdd groupScale actions rows.length pieces.length
        rowRead access tapeAccess ch constant.2 slope.2 := by
  let groups := plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces
    entries ch.x ch.x1 constant slope
  let qb := plonkQuotientPrimeEntry entries
  let data := storedMultiopenDataCosted costs equal read omegaAccess ch.x2 ch.x4 ch.x3 (qb.1, qb.2 + 1) groups.1
  let first := storedFirstOpeningCosted read groups.1
  have hl : groups.1.length = 5 := plonkOpeningMaterialCosted_length costs equal read omegaAccess
    instances fixed sigma rows pieces entries ch.x ch.x1 constant slope
  have hw := plonkOpeningMaterialCosted_dimensions costs equal read omegaAccess
    instances fixed sigma rows pieces entries ch.x ch.x1 constant slope hpieces
  have hdw := storedMultiopenDataCosted_width costs equal read omegaAccess ch.x2 ch.x4 ch.x3
    (qb.1, qb.2 + 1) groups.1 (fun group hgroup => (hw group hgroup).1)
  have hfirst := storedFirstOpeningCosted_width read 2048 groups.1 (fun group hgroup => (hw group hgroup).1)
  have hfirstCost := storedFirstOpeningCosted_cost_le read groups.1
  rewrite [hl] at hfirstCost
  change first.2 ≤ 2 * 5 + read + 2 at hfirstCost
  have hq : qb.2 ≤ access := hentries _
  have hd := storedMultiopenDataCosted_cost_le costs equal read omegaAccess ch.x2 ch.x4 ch.x3
    (qb.1, qb.2 + 1) groups.1 hl (fun group hgroup => (hw group hgroup).1)
    (fun group hgroup => (hw group hgroup).2.2)
  have hdata : data.2 ≤ storedMultiopenDataCostBudget costs equal read omegaAccess ch.x2.2 ch.x4.2 ch.x3.2
      (access + 1) := by
    change data.2 ≤ storedMultiopenDataCostBudget costs equal read omegaAccess ch.x2.2 ch.x4.2 ch.x3.2 (qb.2 + 1) at hd
    unfold storedMultiopenDataCostBudget storedMultiopenBlindCostBudget at *
    omega
  have hm := honestPlonkMaskCosted_cost_le costs equal read omegaAccess groupAdd groupScale generators W
    rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope rowRead access access
    hrows hpieces hdw.1 hfirst hg hentries
  have hmFixed : (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W
      rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope).2 ≤
      honestPlonkMaskCostBudget costs equal read omegaAccess groupAdd groupScale actions rows.length pieces.length
        rowRead access access ch.x.2 ch.x3.2 constant.2 slope.2 (read + 1) (read + 12) access := by
    apply hm.trans
    dsimp only [honestPlonkMaskCostBudget, plonkCommitmentPointsCostBudget, densePolynomialCommitmentCostBudget]
    gcongr
    omega
  rcases hch with ⟨_, _, _, _, _, _, _, hqread, _, hxiread, hzread, hrounds⟩
  have hi := preparedHonestIpaCosted_cost_le costs groupAdd groupScale equal read generators W U data
    ch.x3 ch.xi ch.z ch.ipaRound tape access tapeAccess hdw.2 hg hrounds hW hU hqread hxiread hzread htape
  have hgroups := plonkOpeningMaterialCosted_cost_le costs equal read omegaAccess instances fixed sigma rows pieces
    entries ch.x ch.x1 constant slope rowRead access hinstances hfixed hsigma hrows hpieces hentries
  change groups.2 ≤ plonkOpeningMaterialCostBudget costs equal read omegaAccess actions rows.length pieces.length
    rowRead access ch.x.2 ch.x1.2 constant.2 slope.2 at hgroups
  unfold honestJointRowsCosted
  change groups.2 + (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
    (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope).2 +
    (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data
      ch.x3 ch.xi ch.z ch.ipaRound tape).2 + 1 ≤ _
  unfold honestJointRowsCostBudget preparedHonestIpaCostBudget at *
  omega

end Zcash.Snark.ZeroKnowledge
