import Zcash.Snark.ZeroKnowledge.IpaArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaScalarCost

/-!
# Counted execution and full materialization of the IPA simulator

The costed fields retain all supplied input accesses and primitive operations.
The final materializer forces every round message, the mask commitment, and both
scalar responses into a finite record. Its bound includes work even if a later
encoder rejects an early message. Shared intermediate work may be conservatively
charged again when another output uses it; no output's work is assigned zero
cost merely because the transcript stores a function.

The erasure theorem identifies the complete materialized observation of the
existing witness-free IPA simulator. The runtime theorem uses explicit primitive
prices and a common bound on complete public-input and coin-reader accesses.
Producing the PLONK opening that supplies those public inputs, transcript byte
encoding, and cache processing must be priced by the surrounding composition.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Erase per-field costs without evaluating any extra transcript element. -/
def IpaTranscript.eraseCosts {k : ℕ} {F G : Type*}
    (view : IpaTranscript k (F × ℕ) (G × ℕ)) : IpaTranscript k F G where
  maskCommitment := view.maskCommitment.1
  messages := fun index => ((view.messages index).1.1, (view.messages index).2.1)
  scalar := view.scalar.1
  blind := view.blind.1

/-- A fully materialized IPA observation has an explicit finite message list. -/
@[ext] structure MaterializedIpaTranscript (F G : Type*) where
  maskCommitment : G
  messages : List (G × G)
  scalar : F
  blind : F

/-- The complete materialized observation of the existing IPA transcript. -/
def materializedIpaTranscript {k : ℕ} {F G : Type*}
    (view : IpaTranscript k F G) : MaterializedIpaTranscript F G where
  maskCommitment := view.maskCommitment
  messages := List.ofFn view.messages
  scalar := view.scalar
  blind := view.blind

/-- Force all transcript fields and retain their complete arithmetic and reader costs. -/
def materializeIpaCosted {k : ℕ} {F G : Type*}
    (view : IpaTranscript k (F × ℕ) (G × ℕ)) : MaterializedIpaTranscript F G × ℕ :=
  let rounds := ofFnCosted fun index =>
    let message := view.messages index
    ((message.1.1, message.2.1), message.1.2 + message.2.2 + 1)
  ({ maskCommitment := view.maskCommitment.1, messages := rounds.1,
      scalar := view.scalar.1, blind := view.blind.1 },
    rounds.2 + view.maskCommitment.2 + view.scalar.2 + view.blind.2 + 1)

/-- The counted materialization retains every original message and scalar. -/
theorem materializeIpaCosted_result {k : ℕ} {F G : Type*}
    (view : IpaTranscript k (F × ℕ) (G × ℕ)) :
    (materializeIpaCosted view).1 = materializedIpaTranscript view.eraseCosts := by
  simp only [materializeIpaCosted, ofFnCosted_result, materializedIpaTranscript, IpaTranscript.eraseCosts]

/-- Full materialization pays for every output field, even if a later encoder stops early. -/
theorem materializeIpaCosted_cost_le {k : ℕ} {F G : Type*}
    (view : IpaTranscript k (F × ℕ) (G × ℕ)) (maskBound messageBound scalarBound blindBound : ℕ)
    (hmask : view.maskCommitment.2 ≤ maskBound)
    (hmessages : ∀ index, (view.messages index).1.2 ≤ messageBound ∧
      (view.messages index).2.2 ≤ messageBound)
    (hscalar : view.scalar.2 ≤ scalarBound) (hblind : view.blind.2 ≤ blindBound) :
    (materializeIpaCosted view).2 ≤
      k * (2 * messageBound + 2) + k * k + maskBound + scalarBound + blindBound + 2 := by
  have hread (index : Fin k) :
      (view.messages index).1.2 + (view.messages index).2.2 + 1 ≤ 2 * messageBound + 1 := by
    have h := hmessages index
    omega
  have h := ofFnCosted_cost_le (fun index : Fin k =>
    (((view.messages index).1.1, (view.messages index).2.1),
      (view.messages index).1.2 + (view.messages index).2.2 + 1)) (2 * messageBound + 1) hread
  dsimp only [materializeIpaCosted]
  calc
    _ ≤ (k * (2 * messageBound + 1 + 1) + k * k + 1) +
        maskBound + scalarBound + blindBound + 1 := by omega
    _ = _ := by ring

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Sample each round point with its full coin, blinding-generator, and scalar-multiplication cost. -/
def ipaSimulatorRoundCosted (costs : IpaOperationCosts) {k : ℕ} (W : G × ℕ)
    (coins : Fin k → (F × F) × ℕ) (index : Fin k) : (G × ℕ) × (G × ℕ) :=
  let coin := coins index
  ((coin.1.1 • W.1, coin.2 + W.2 + costs.groupScale + 1),
    (coin.1.2 • W.1, coin.2 + W.2 + costs.groupScale + 1))

/-- Erasing the two costs gives exactly the original blinded zero-message pair. -/
theorem ipaSimulatorRoundCosted_result (costs : IpaOperationCosts) {k : ℕ} (W : G × ℕ)
    (coins : Fin k → (F × F) × ℕ) (index : Fin k) :
    ((ipaSimulatorRoundCosted costs W coins index).1.1,
      (ipaSimulatorRoundCosted costs W coins index).2.1) =
      blindIpaMessages W.1 (fun _ => (0, 0)) (fun index => (coins index).1) index := by
  simp only [ipaSimulatorRoundCosted, blindIpaMessages, zero_add]

/-- Execute all IPA fields with costs that can be retained by a full materializer. -/
def ipaSimulatorFromCoinsCosted [DecidableEq F] (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (roundCoins : Fin k → (F × F) × ℕ)
    (scalarCoin finalBlind : F × ℕ) : IpaTranscript k (F × ℕ) (G × ℕ) :=
  let chosen := chooseIpaScalarCosted costs.fieldMultiply costs.fieldInverse costs.fieldEqual
    pub.point pub.rounds scalarCoin
  let messages := ipaSimulatorRoundCosted costs pub.W roundCoins
  { maskCommitment := completeIpaMaskCosted costs pub (fun index =>
      let message := messages index
      ((message.1.1, message.2.1), message.1.2 + message.2.2 + 1)) chosen finalBlind,
    messages := messages, scalar := chosen, blind := finalBlind }

/-- The counted field construction is exactly the existing witness-free IPA simulator. -/
theorem ipaSimulatorFromCoinsCosted_result [DecidableEq F] (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (roundCoins : Fin k → (F × F) × ℕ)
    (scalarCoin finalBlind : F × ℕ) :
    (ipaSimulatorFromCoinsCosted costs pub roundCoins scalarCoin finalBlind).eraseCosts =
      ipaSimulatorFromCoins pub.erase (fun index => (roundCoins index).1) scalarCoin.1 finalBlind.1 := by
  have hmessages :
      (fun index => ((ipaSimulatorRoundCosted costs pub.W roundCoins index).1.1,
        (ipaSimulatorRoundCosted costs pub.W roundCoins index).2.1)) =
      blindIpaMessages pub.W.1 (fun _ => (0, 0)) (fun index => (roundCoins index).1) := by
    funext index
    exact ipaSimulatorRoundCosted_result costs pub.W roundCoins index
  simp only [ipaSimulatorFromCoinsCosted, IpaTranscript.eraseCosts, completeIpaMaskCosted_result,
    chooseIpaScalarCosted_result, ipaSimulatorFromCoins, completeIpaTranscript,
    hmessages]
  rfl

/-- Full materialization retains the existing simulator's complete finite observation. -/
theorem materializedIpaSimulatorCosted_result [DecidableEq F] (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (roundCoins : Fin k → (F × F) × ℕ)
    (scalarCoin finalBlind : F × ℕ) :
    (materializeIpaCosted (ipaSimulatorFromCoinsCosted costs pub roundCoins scalarCoin finalBlind)).1 =
      materializedIpaTranscript
        (ipaSimulatorFromCoins pub.erase (fun index => (roundCoins index).1) scalarCoin.1 finalBlind.1) := by
  rw [materializeIpaCosted_result, ipaSimulatorFromCoinsCosted_result]

/-- Complete input accesses for the public IPA data have a common upper bound. -/
def IpaPublicCosted.ReadBound {k : ℕ} (pub : IpaPublicCosted k F G) (bound : ℕ) : Prop :=
  (∀ index, (pub.generators index).2 ≤ bound) ∧
    (∀ index, (pub.rounds index).2 ≤ bound) ∧
    pub.U.2 ≤ bound ∧ pub.W.2 ≤ bound ∧ pub.commitment.2 ≤ bound ∧
    pub.point.2 ≤ bound ∧ pub.value.2 ≤ bound ∧ pub.xi.2 ≤ bound ∧ pub.z.2 ≤ bound

/-- A uniform read bound specializes the checked public scalar-test budget. -/
def ipaSimulatorScalarCostBudget (costs : IpaOperationCosts) (k access : ℕ) : ℕ :=
  2 * access + k * (access + k * (costs.fieldMultiply + 1) + costs.fieldInverse + costs.fieldEqual + 5) +
    k * k + 2

/-- Full IPA materialization budget, including generation and later reads of every round point. -/
def ipaSimulatorCostBudget (costs : IpaOperationCosts) (k access : ℕ) : ℕ :=
  10 * access + 2 * ipaSimulatorScalarCostBudget costs k access +
    completeIpaMaskCostBudget costs k access access (4 * access + 2 * costs.groupScale + 3) +
    k * (4 * access + 2 * costs.groupScale + 4) + k * k + 2

/-- The complete materialized IPA simulator has a bound on all its arithmetic and input accesses. -/
theorem materializedIpaSimulatorCosted_cost_le [DecidableEq F] (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (roundCoins : Fin k → (F × F) × ℕ)
    (scalarCoin finalBlind : F × ℕ) (access : ℕ)
    (hpub : pub.ReadBound access) (hcoins : ∀ index, (roundCoins index).2 ≤ access)
    (hscalar : scalarCoin.2 ≤ access) (hblind : finalBlind.2 ≤ access) :
    (materializeIpaCosted (ipaSimulatorFromCoinsCosted costs pub roundCoins scalarCoin finalBlind)).2 ≤
      ipaSimulatorCostBudget costs k access := by
  rcases hpub with ⟨hgenerator, hround, hU, hW, hcommitment, hpoint, hvalue, hxi, hz⟩
  let chosen := chooseIpaScalarCosted costs.fieldMultiply costs.fieldInverse costs.fieldEqual
    pub.point pub.rounds scalarCoin
  let messages := ipaSimulatorRoundCosted costs pub.W roundCoins
  have hchosen : chosen.2 ≤ ipaSimulatorScalarCostBudget costs k access := by
    have h := chooseIpaScalarCosted_cost_le costs.fieldMultiply costs.fieldInverse costs.fieldEqual
      pub.point pub.rounds scalarCoin access hround
    dsimp only [chosen, ipaSimulatorScalarCostBudget]
    omega
  have hmessages (index : Fin k) :
      (messages index).1.2 ≤ 2 * access + costs.groupScale + 1 ∧
        (messages index).2.2 ≤ 2 * access + costs.groupScale + 1 := by
    have h := hcoins index
    dsimp only [messages, ipaSimulatorRoundCosted]
    constructor <;> omega
  have hpairs (index : Fin k) :
      (messages index).1.2 + (messages index).2.2 + 1 ≤
        4 * access + 2 * costs.groupScale + 3 := by
    have h := hmessages index
    omega
  have hmask := completeIpaMaskCosted_cost_le costs pub (fun index =>
      (((messages index).1.1, (messages index).2.1),
        (messages index).1.2 + (messages index).2.2 + 1))
    chosen finalBlind access access (4 * access + 2 * costs.groupScale + 3)
    hround hgenerator hpairs
  have hmaskBound :
      (completeIpaMaskCosted costs pub (fun index =>
        (((messages index).1.1, (messages index).2.1),
          (messages index).1.2 + (messages index).2.2 + 1)) chosen finalBlind).2 ≤
      9 * access + ipaSimulatorScalarCostBudget costs k access +
        completeIpaMaskCostBudget costs k access access (4 * access + 2 * costs.groupScale + 3) := by
    have hzero := hgenerator 0
    omega
  have htotal := materializeIpaCosted_cost_le
    (ipaSimulatorFromCoinsCosted costs pub roundCoins scalarCoin finalBlind)
    (9 * access + ipaSimulatorScalarCostBudget costs k access +
      completeIpaMaskCostBudget costs k access access (4 * access + 2 * costs.groupScale + 3))
    (2 * access + costs.groupScale + 1) (ipaSimulatorScalarCostBudget costs k access) access
    hmaskBound hmessages hchosen hblind
  calc
    _ ≤ k * (2 * (2 * access + costs.groupScale + 1) + 2) + k * k +
        (9 * access + ipaSimulatorScalarCostBudget costs k access +
          completeIpaMaskCostBudget costs k access access (4 * access + 2 * costs.groupScale + 3)) +
        ipaSimulatorScalarCostBudget costs k access + access + 2 := htotal
    _ = _ := by unfold ipaSimulatorCostBudget; ring

end Zcash.Snark.ZeroKnowledge
