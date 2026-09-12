import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeCost

/-!
# Complete stored-tape preparation and access bounds

The bounds use the actual input bit-list length and the original word count.
They include both materialization passes, every eager scalar read, and the full
list traversal for each later challenge or private-coin access.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A common bound for all readers generated from the original complete tape. -/
def plonkStoredTapeReadBudget (actions k read : ℕ) : ℕ :=
  4 * ((k + 11) + plonkSimulatorSampleCount actions k) + 2 * read + 25

/-- All prepared readers satisfy a bound derived from their actual generated field list. -/
theorem storedPlonkSimulatorTapesCosted_readBound (actions k read : ℕ) (bits : List Bool) :
    Challenges.ReadBound (storedPlonkSimulatorTapesCosted actions k read bits).1.challenges
        (plonkStoredTapeReadBudget actions k read) ∧
      (storedPlonkSimulatorTapesCosted actions k read bits).1.coins.ReadBound
        (plonkStoredTapeReadBudget actions k read) := by
  let count := (k + 11) + plonkSimulatorSampleCount actions k
  let fields := storedFieldTapeCosted count read bits
  have hlength : fields.1.length = count := ofFnCosted_length _
  have hch := storedPlonkChallengesCosted_readBound k read fields.1 0
  have hcoins := storedPlonkCoinsCosted_readBound actions k read fields.1 (k + 11)
  rw [hlength] at hch hcoins
  refine ⟨?_, hcoins⟩
  have haccess : 2 * count + read + 11 ≤ plonkStoredTapeReadBudget actions k read := by
    dsimp only [plonkStoredTapeReadBudget, count]
    omega
  rcases hch with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hround⟩
  exact ⟨h0.trans haccess, h1.trans haccess, h2.trans haccess, h3.trans haccess,
    h4.trans haccess, h5.trans haccess, h6.trans haccess, h7.trans haccess,
    h8.trans haccess, h9.trans haccess, h10.trans haccess, fun index => (hround index).trans haccess⟩

/-- An explicit polynomial budget for both packing passes and all eager tape preparation. -/
def plonkStoredTapeCostBudget (actions k read bitLength : ℕ) : ℕ :=
  let count := (k + 11) + plonkSimulatorSampleCount actions k
  (count * (512 * (2 * bitLength + read + 4) + 264195) + count * count + 1) +
    (count * (512 * (2 * bitLength + read + 4) + 264194) + count * count + 1) +
    (11 * (2 * count + read + 11) + 24) + (8 * count + 4 * read + 59) + 5

/-- The entire tape producer, rather than only its sampling count, satisfies the concrete budget. -/
theorem storedPlonkSimulatorTapesCosted_cost_le (actions k read : ℕ) (bits : List Bool) :
    (storedPlonkSimulatorTapesCosted actions k read bits).2 ≤
      plonkStoredTapeCostBudget actions k read bits.length := by
  let count := (k + 11) + plonkSimulatorSampleCount actions k
  let raw := storedRawTapeCosted count read bits
  let fields := storedFieldTapeCosted count read bits
  have hlength : fields.1.length = count := ofFnCosted_length _
  have hraw := storedRawTapeCosted_cost_le count read bits
  have hfields := storedFieldTapeCosted_cost_le count read bits
  have hch := storedPlonkChallengesCosted_cost_le k read fields.1 0
  have hcoins := storedPlonkCoinsCosted_cost_le actions k read fields.1 (k + 11)
  rw [hlength] at hch hcoins
  change raw.2 + fields.2 + (storedPlonkChallengesCosted k read fields.1 0).2 +
    (storedPlonkCoinsCosted actions k read fields.1 (k + 11)).2 + 5 ≤ _
  dsimp only [plonkStoredTapeCostBudget]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hraw hfields) hch) hcoins) 5

end Zcash.Snark.ZeroKnowledge
