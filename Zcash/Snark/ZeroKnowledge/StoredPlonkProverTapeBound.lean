import Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapes

namespace Zcash.Snark.ZeroKnowledge

/-- Common complete verifier-challenge reader price from the original real tape size. -/
def storedPlonkProverTapeReadBudget (actions read : ℕ) : ℕ := 2 * (22 + fieldSampleCount actions) + read + 11

/-- Original real-prover bit packing, field reduction, private split, and challenge-preparation budget. -/
def storedPlonkProverTapeCostBudget (actions read bitLength : ℕ) : ℕ :=
  let count := 22 + fieldSampleCount actions
  (count * (512 * (2 * bitLength + read + 4) + 264195) + count * count + 1) +
    (count * (512 * (2 * bitLength + read + 4) + 264194) + count * count + 1) +
    (count * (read + 2) + 1) + (11 * (2 * count + read + 11) + 24) + 4

/-- Every bit tape satisfies the same fully counted real-prover preparation budget. -/
theorem storedPlonkProverTapesCosted_cost_le (actions read : ℕ) (bits : List Bool) :
    (storedPlonkProverTapesCosted actions read bits).2 ≤ storedPlonkProverTapeCostBudget actions read bits.length := by
  let count := 22 + fieldSampleCount actions
  let fields := storedFieldTapeCosted count read bits
  have hl : fields.1.length = count := ofFnCosted_length _
  have hr := storedRawTapeCosted_cost_le count read bits
  have hf := storedFieldTapeCosted_cost_le count read bits
  have hs := splitListCosted_cost_le read 22 fields.1
  have hc := storedPlonkChallengesCosted_cost_le 11 read fields.1 0
  rewrite [hl] at hs hc
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hr hf) hs) hc) 4

/-- The challenge reader bound is derived from the actual produced field-list length. -/
theorem storedPlonkProverTapesCosted_readBound (actions read : ℕ) (bits : List Bool) :
    Challenges.ReadBound (storedPlonkProverTapesCosted actions read bits).1.challenges
      (storedPlonkProverTapeReadBudget actions read) := by
  have h := storedPlonkChallengesCosted_readBound 11 read
    (storedFieldTapeCosted (22 + fieldSampleCount actions) read bits).1 0
  have hl : (storedFieldTapeCosted (22 + fieldSampleCount actions) read bits).1.length =
      22 + fieldSampleCount actions := ofFnCosted_length _
  rewrite [hl] at h
  exact h

end Zcash.Snark.ZeroKnowledge
