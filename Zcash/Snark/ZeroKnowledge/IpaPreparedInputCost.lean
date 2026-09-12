import Zcash.Snark.ZeroKnowledge.IpaSimulatorCost

/-!
# Composing a computed public opening with the complete IPA simulator

The opening and scalar public inputs are computed before they are stored. Their
full costs remain in preparation; subsequent stored-field accesses cost one unit.
Generator and challenge readers keep their complete access costs for every later
use. The final operation materializes every field of the original IPA transcript.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Store the computed IPA input while retaining every complete preparation cost. -/
def prepareIpaPublicCosted {k : ℕ} {F G : Type*}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ) :
    IpaPublicCosted k F G × ℕ :=
  ({ generators := generators, W := (W.1, 1), U := (U.1, 1),
      commitment := (opening.1.1, 1), point := (q.1, 1), value := (opening.1.2, 1),
      xi := (xi.1, 1), z := (z.1, 1), rounds := rounds },
    opening.2 + W.2 + U.2 + q.2 + xi.2 + z.2 + 10)

/-- Input preparation preserves the original public opening and every challenge. -/
theorem prepareIpaPublicCosted_result {k : ℕ} {F G : Type*}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ) :
    (prepareIpaPublicCosted generators W U opening q xi z rounds).1.erase =
      { generators := fun index => (generators index).1, W := W.1, U := U.1,
        commitment := opening.1.1, point := q.1, value := opening.1.2,
        xi := xi.1, z := z.1, rounds := fun index => (rounds index).1 } := rfl

/-- All computed inputs are paid for before they are stored. -/
theorem prepareIpaPublicCosted_cost {k : ℕ} {F G : Type*}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ) :
    (prepareIpaPublicCosted generators W U opening q xi z rounds).2 =
      opening.2 + W.2 + U.2 + q.2 + xi.2 + z.2 + 10 := rfl

/-- Prepared scalar fields have unit access, while finite readers retain their full bounds. -/
theorem prepareIpaPublicCosted_readBound {k : ℕ} {F G : Type*}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ)
    (access : ℕ) (hpositive : 1 ≤ access)
    (hgenerators : ∀ index, (generators index).2 ≤ access)
    (hrounds : ∀ index, (rounds index).2 ≤ access) :
    (prepareIpaPublicCosted generators W U opening q xi z rounds).1.ReadBound access :=
  ⟨hgenerators, hrounds, hpositive, hpositive, hpositive, hpositive, hpositive, hpositive, hpositive⟩

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F]

/-- Prepare the computed public opening, run the IPA algorithm, and force every output field. -/
def preparedIpaSimulatorCosted (costs : IpaOperationCosts) {k : ℕ}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ)
    (roundCoins : Fin k → (F × F) × ℕ) (scalarCoin finalBlind : F × ℕ) :
    MaterializedIpaTranscript F G × ℕ :=
  let input := prepareIpaPublicCosted generators W U opening q xi z rounds
  let result := materializeIpaCosted (ipaSimulatorFromCoinsCosted costs input.1 roundCoins scalarCoin finalBlind)
  (result.1, input.2 + result.2 + 1)

/-- Erasure retains the original IPA simulator on precisely the prepared public input. -/
theorem preparedIpaSimulatorCosted_result (costs : IpaOperationCosts) {k : ℕ}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ)
    (roundCoins : Fin k → (F × F) × ℕ) (scalarCoin finalBlind : F × ℕ) :
    (preparedIpaSimulatorCosted costs generators W U opening q xi z rounds roundCoins scalarCoin finalBlind).1 =
      materializedIpaTranscript
        (ipaSimulatorFromCoins (prepareIpaPublicCosted generators W U opening q xi z rounds).1.erase
          (fun index => (roundCoins index).1) scalarCoin.1 finalBlind.1) :=
  materializedIpaSimulatorCosted_result _ _ _ _ _

/-- The composed bound pays for the complete opening once, then every IPA output and access. -/
theorem preparedIpaSimulatorCosted_cost_le (costs : IpaOperationCosts) {k : ℕ}
    (generators : Fin (2 ^ k) → G × ℕ) (W U : G × ℕ)
    (opening : (G × F) × ℕ) (q xi z : F × ℕ) (rounds : Fin k → F × ℕ)
    (roundCoins : Fin k → (F × F) × ℕ) (scalarCoin finalBlind : F × ℕ)
    (access : ℕ) (hpositive : 1 ≤ access)
    (hgenerators : ∀ index, (generators index).2 ≤ access)
    (hrounds : ∀ index, (rounds index).2 ≤ access)
    (hW : W.2 ≤ access) (hU : U.2 ≤ access)
    (hq : q.2 ≤ access) (hxi : xi.2 ≤ access) (hz : z.2 ≤ access)
    (hcoins : ∀ index, (roundCoins index).2 ≤ access)
    (hscalar : scalarCoin.2 ≤ access) (hblind : finalBlind.2 ≤ access) :
    (preparedIpaSimulatorCosted costs generators W U opening q xi z rounds roundCoins scalarCoin finalBlind).2 ≤
      opening.2 + 5 * access + ipaSimulatorCostBudget costs k access + 11 := by
  have hinput := prepareIpaPublicCosted_readBound generators W U opening q xi z rounds
    access hpositive hgenerators hrounds
  have h := materializedIpaSimulatorCosted_cost_le costs
    (prepareIpaPublicCosted generators W U opening q xi z rounds).1 roundCoins scalarCoin finalBlind
    access hinput hcoins hscalar hblind
  dsimp only [preparedIpaSimulatorCosted]
  rw [prepareIpaPublicCosted_cost]
  omega

end Zcash.Snark.ZeroKnowledge
