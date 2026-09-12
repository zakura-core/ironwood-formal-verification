import Zcash.Snark.ZeroKnowledge.PlonkCoinReadCost
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost
import Zcash.Snark.ZeroKnowledge.PlonkChallenges

/-!
# Verifier challenge preparation from the stored field tape

The eleven scalar fields are read while constructing the challenge record. The
round family retains its indexed reader. Preparation pays for all eager reads
and the record; subsequent access prices conservatively retain the reader cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Prepare the original challenge record, charging every eager scalar read. -/
def storedPlonkChallengesCosted (k read : ℕ) (fields : List Fp) (base : ℕ) :
    Challenges k (Fp × ℕ) × ℕ :=
  let ch := plonkChallengesFromTape (k := k)
    (fun index => storedPlonkFieldReadCosted read fields base index.val)
  (ch, ch.theta.2 + ch.beta.2 + ch.gamma.2 + ch.y.2 + ch.x.2 +
    ch.x1.2 + ch.x2.2 + ch.x3.2 + ch.x4.2 + ch.xi.2 + ch.z.2 + 24)

/-- Erasure gives every original challenge at its exact tape position. -/
theorem storedPlonkChallengesCosted_result (k read : ℕ) (fields : List Fp) (base : ℕ) :
    Challenges.eraseCosts (storedPlonkChallengesCosted k read fields base).1 =
      plonkChallengesFromTape (k := k) (fun index => fields.getD (base + index.val) 0) := by
  simp only [storedPlonkChallengesCosted, Challenges.eraseCosts, plonkChallengesFromTape,
    storedPlonkFieldReadCosted_result]

/-- All scalar and round accesses have the complete stored-list read bound. -/
theorem storedPlonkChallengesCosted_readBound (k read : ℕ) (fields : List Fp) (base : ℕ) :
    Challenges.ReadBound (storedPlonkChallengesCosted k read fields base).1
      (2 * fields.length + read + 11) := by
  exact ⟨storedPlonkFieldReadCosted_cost_le read fields base 0,
    storedPlonkFieldReadCosted_cost_le read fields base 1,
    storedPlonkFieldReadCosted_cost_le read fields base 2,
    storedPlonkFieldReadCosted_cost_le read fields base 3,
    storedPlonkFieldReadCosted_cost_le read fields base 4,
    storedPlonkFieldReadCosted_cost_le read fields base 5,
    storedPlonkFieldReadCosted_cost_le read fields base 6,
    storedPlonkFieldReadCosted_cost_le read fields base 7,
    storedPlonkFieldReadCosted_cost_le read fields base 8,
    storedPlonkFieldReadCosted_cost_le read fields base 9,
    storedPlonkFieldReadCosted_cost_le read fields base 10,
    fun index => storedPlonkFieldReadCosted_cost_le read fields base (11 + index.val)⟩

/-- Preparation includes eleven full list reads and fixed record construction. -/
theorem storedPlonkChallengesCosted_cost_le (k read : ℕ) (fields : List Fp) (base : ℕ) :
    (storedPlonkChallengesCosted k read fields base).2 ≤
      11 * (2 * fields.length + read + 11) + 24 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ :=
    storedPlonkChallengesCosted_readBound k read fields base
  change (storedPlonkChallengesCosted k read fields base).1.theta.2 +
    (storedPlonkChallengesCosted k read fields base).1.beta.2 +
    (storedPlonkChallengesCosted k read fields base).1.gamma.2 +
    (storedPlonkChallengesCosted k read fields base).1.y.2 +
    (storedPlonkChallengesCosted k read fields base).1.x.2 +
    (storedPlonkChallengesCosted k read fields base).1.x1.2 +
    (storedPlonkChallengesCosted k read fields base).1.x2.2 +
    (storedPlonkChallengesCosted k read fields base).1.x3.2 +
    (storedPlonkChallengesCosted k read fields base).1.x4.2 +
    (storedPlonkChallengesCosted k read fields base).1.xi.2 +
    (storedPlonkChallengesCosted k read fields base).1.z.2 + 24 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
