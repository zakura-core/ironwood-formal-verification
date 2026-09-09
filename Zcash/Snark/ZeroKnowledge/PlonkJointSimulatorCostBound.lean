import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCost
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorBudget
import Zcash.Snark.ZeroKnowledge.PlonkJointStoredBounds

/-!
# Complete joint-simulator cost bound

Every prepared mask reader obtains its size and access bounds from the actual
constructor. The quotient, opening, and IPA budgets therefore compose without
an arbitrary claim-preparation or expected-quotient callback premise.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The complete joint simulation satisfies the composite budget for all challenges and coins. -/
theorem plonkJointSimulatorCosted_cost_le (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ) (key : StoredPlonkKey)
    (ch : Challenges 11 (Fp × ℕ)) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ)
    (baseRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ baseRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ baseRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ baseRead)
    (hgenerators : ∀ index, (generators index).2 ≤ baseRead)
    (hW : W.2 ≤ baseRead) (hU : U.2 ≤ baseRead) (hch : Challenges.ReadBound ch baseRead)
    (hblinds : ∀ index, (blinds index).2 ≤ baseRead)
    (hobservations : ∀ column index, (observations column index).2 ≤ baseRead)
    (hlinear : linear.2 ≤ baseRead) (hfirst : firstGroup.2 ≤ baseRead)
    (hroundCoins : ∀ index, (roundCoins index).2 ≤ baseRead)
    (hscalar : scalarCoin.2 ≤ baseRead) (hblind : finalBlind.2 ≤ baseRead) :
    (plonkJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess instances fixed sigma
      generators W U key ch blinds observations linear firstGroup roundCoins scalarCoin finalBlind).2 ≤
      plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess actions baseRead W.2 key ch := by
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
  let access := plonkJointAccessBudget actions baseRead read key
  have hbase : baseRead ≤ access := by dsimp only [access, plonkJointAccessBudget]; omega
  have hunit : 1 ≤ access := by dsimp only [access, plonkJointAccessBudget]; omega
  have hread : read + 1 ≤ access := by dsimp only [access, plonkJointAccessBudget]; omega
  rcases hch with ⟨htheta, hbeta, hgamma, hy, hxRead, hx1, hx2, hq, hx4, hxi, hz, hrounds⟩
  have hviewsLength : views.1.length = 22 * actions :=
    plonkMaskStoredViews_length ipaCosts.groupScale W blinds observations linear firstGroup read
  have hviewsRead : ∀ column ∈ views.1, ∀ index, (column index).2 ≤ access := by
    intro column hcolumn index
    have h := plonkMaskStoredViews_readBound ipaCosts.groupScale W blinds observations linear firstGroup
      read column hcolumn index
    dsimp only [access, plonkJointAccessBudget]
    omega
  have hpoints : ∀ index, (points index).2 ≤ access := by
    intro index
    have h := plonkMaskStoredPoints_cost_le ipaCosts.groupScale W blinds observations linear firstGroup read index
    change (points index).2 ≤ _ at h
    dsimp only [access, plonkJointAccessBudget]
    omega
  have hinputs : ∀ index, (key.lookupInputCosted read index).2 ≤ access := by
    intro index
    have h := key.lookupInputCosted_cost_le read index
    dsimp only [access, plonkJointAccessBudget]
    omega
  have htables : ∀ index, (key.lookupTableCosted read index).2 ≤ access := by
    intro index
    have h := key.lookupTableCosted_cost_le read index
    dsimp only [access, plonkJointAccessBudget]
    omega
  have hmask := materializedPlonkMaskSimulatorCosted_cost_le ipaCosts.groupScale W blinds observations
    linear firstGroup baseRead hblinds hobservations hlinear hfirst
  change mask.2 ≤ _ at hmask
  have hviews := plonkMaskStoredViews_cost_le ipaCosts.groupScale W blinds observations linear firstGroup read
  change views.2 ≤ _ at hviews
  have hhx := plonkVerifierHxCosted_cost_le fieldCosts node equal read omegaAccess instances fixed sigma views.1
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    (key.omega, read + 1) key.n key.blindingFactors ch.beta ch.gamma ch.x ch.y
    (key.delta, read + 1) ch.theta key.chunkLen access hunit
    (fun action row => (hinstances action row).trans hbase)
    (fun column row => (hfixed column row).trans hbase)
    (fun column row => (hsigma column row).trans hbase) hviewsRead hinputs htables
    hread (hbeta.trans hbase) (hgamma.trans hbase) (hxRead.trans hbase) hread (htheta.trans hbase)
  change hx.2 ≤ _ at hhx
  rw [hviewsLength] at hhx
  have hopening := plonkPublicOpeningCosted_cost_le fieldCosts ipaCosts.groupAdd ipaCosts.groupScale
    equal read omegaAccess instances fixed sigma generators W points views.1 ch.x ch.x1 ch.x2 ch.x4 ch.x3
    (hx.1, 1) (mask.1.2.2.1, 1) (mask.1.2.2.2, 1) access access access access
    (fun action row => (hinstances action row).trans hbase)
    (fun column row => (hfixed column row).trans hbase)
    (fun column row => (hsigma column row).trans hbase)
    (fun index => (hgenerators index).trans hbase) hpoints hviewsRead
  change opening.2 ≤ _ at hopening
  rw [hviewsLength] at hopening
  change opening.2 ≤ plonkPublicOpeningCostBudget fieldCosts ipaCosts.groupAdd ipaCosts.groupScale
    equal read omegaAccess actions (22 * actions) access access W.2 access access
    ch.x.2 ch.x1.2 ch.x2.2 ch.x4.2 ch.x3.2 1 1 1 at hopening
  have hipa := preparedIpaSimulatorCosted_cost_le ipaCosts generators W U opening ch.x3 ch.xi ch.z ch.ipaRound
    roundCoins scalarCoin finalBlind access hunit (fun index => (hgenerators index).trans hbase)
    (fun index => (hrounds index).trans hbase) (hW.trans hbase) (hU.trans hbase)
    (hq.trans hbase) (hxi.trans hbase) (hz.trans hbase)
    (fun index => (hroundCoins index).trans hbase) (hscalar.trans hbase) (hblind.trans hbase)
  change ipa.2 ≤ _ at hipa
  change mask.2 + views.2 + hx.2 + ipa.2 + 3 * (read + 1) + 4 ≤ _
  dsimp only [plonkJointSimulatorCostBudget]
  change _ ≤ ((22 * actions + 10) * (baseRead + W.2 + ipaCosts.groupScale + 2) +
    (22 * actions + 10) * (22 * actions + 10) +
    (22 * actions) * (5 * baseRead + 32) + (22 * actions) * (22 * actions) + 2 * baseRead + 3) +
    ((22 * actions) * 3 + 1) +
    plonkVerifierHxCostBudget fieldCosts node equal read omegaAccess actions (22 * actions)
      access ch.x.2 ch.y.2 (key.gatesCosted read) (key.layoutCosted read)
      (key.lookupInputCosted read) (key.lookupTableCosted read) key.n key.blindingFactors key.chunkLen +
    (plonkPublicOpeningCostBudget fieldCosts ipaCosts.groupAdd ipaCosts.groupScale equal read omegaAccess
      actions (22 * actions) access access W.2 access access ch.x.2 ch.x1.2 ch.x2.2 ch.x4.2 ch.x3.2 1 1 1 +
      5 * access + ipaSimulatorCostBudget ipaCosts 11 access + 11) + 3 * (read + 1) + 4
  omega

end Zcash.Snark.ZeroKnowledge
