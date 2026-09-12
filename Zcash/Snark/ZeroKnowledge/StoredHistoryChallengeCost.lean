import Zcash.Snark.ZeroKnowledge.StoredRawFieldCost
import Zcash.Snark.ZeroKnowledge.PlonkChallengeReadCost
import Zcash.Snark.ZeroKnowledge.StoredChallengePrices
import Zcash.Snark.ZeroKnowledge.RawChallenges
import Zcash.Snark.ZeroKnowledge.OracleSchedule

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Reduce the received raw history and prepare every original typed challenge reader. -/
def storedHistoryChallengesCosted (read : ℕ) (history : List (Fin challengeDigestCard)) :
    Challenges 11 (Fp × ℕ) × ℕ :=
  let fields := storedRawFieldsCosted 22 read history
  let challenges := storedPlonkChallengesCosted 11 read fields.1 0
  (challenges.1, fields.2 + challenges.2 + 2)

/-- Unreceived challenges are exactly the original oracle computation's zero-filled history. -/
theorem storedHistoryChallengesCosted_result (read : ℕ) (history : List (Fin challengeDigestCard)) :
    Challenges.eraseCosts (storedHistoryChallengesCosted read history).1 =
      plonkChallengesFromDigests 11 (oracleHistoryTape 0 history) := by
  unfold storedHistoryChallengesCosted
  rewrite [storedPlonkChallengesCosted_result, storedRawFieldsCosted_result]
  apply congrArg (plonkChallengesFromTape (k := 11))
  funext index
  have h := getDListCosted_ofFn_result read (0 : Fp)
    (fun index : Fin 22 => ((history.getD index.val 0).val : Fp)) index
  simpa only [getDListCosted_result, Nat.zero_add, oracleHistoryTape] using h

/-- All later challenge reads have a fixed bound independent of the received values. -/
theorem storedHistoryChallengesCosted_readBound (read : ℕ) (history : List (Fin challengeDigestCard)) :
    Challenges.ReadBound (storedHistoryChallengesCosted read history).1 (read + 55) := by
  have h := storedPlonkChallengesCosted_readBound 11 read (storedRawFieldsCosted 22 read history).1 0
  rewrite [storedRawFieldsCosted_length] at h
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The complete preparation pays every history lookup, wide reduction, and eager scalar load. -/
theorem storedHistoryChallengesCosted_cost_le (read : ℕ) (history : List (Fin challengeDigestCard)) :
    (storedHistoryChallengesCosted read history).2 ≤
      22 * (2 * history.length + read + 4) + 485 + 11 * (read + 55) + 26 := by
  have hf := storedRawFieldsCosted_cost_le 22 read history
  have hc := storedPlonkChallengesCosted_cost_le 11 read (storedRawFieldsCosted 22 read history).1 0
  rewrite [storedRawFieldsCosted_length] at hc
  dsimp only [storedHistoryChallengesCosted]
  omega

/-- Actual challenge-position prices agree with the same fixed model used by the full prover budget. -/
theorem storedHistoryChallengesCosted_prices (read : ℕ) (history : List (Fin challengeDigestCard)) :
    Challenges.readPrices (storedHistoryChallengesCosted read history).1 =
      Challenges.readPrices (storedPlonkChallengePriceModel 11 read) := by
  let fields := storedRawFieldsCosted 22 read history
  have hl : fields.1.length = 22 := storedRawFieldsCosted_length 22 read history
  have hp (index : Fin 22) : (storedPlonkFieldReadCosted read fields.1 0 index.val).2 =
      2 * index.val + read + 11 := by
    have hi : 0 + index.val < fields.1.length := by rewrite [hl]; omega
    simpa only [Nat.zero_add] using storedPlonkFieldReadCosted_cost_of_lt read fields.1 0 index.val hi
  change plonkChallengesFromTape (k := 11) (fun index => (storedPlonkFieldReadCosted read fields.1 0 index.val).2) =
    plonkChallengesFromTape (fun index => 2 * index.val + read + 11)
  exact congrArg (plonkChallengesFromTape (k := 11)) (funext hp)

/-- Every raw reply agrees with the observer's totalized field schedule for a reachable history. -/
theorem storedHistoryChallengesCosted_agreement (read : ℕ) (history : List (Fin challengeDigestCard))
    (hlength : history.length ≤ 22) (index : ℕ) :
    (((oracleHistoryTape 0 history index).val) : Fp) =
      plonkAttemptChallenge (Challenges.eraseCosts (storedHistoryChallengesCosted read history).1) index := by
  rewrite [storedHistoryChallengesCosted_result, plonkChallengesFromDigests_read]
  by_cases hi : index < 22
  · rewrite [if_pos hi]
    rfl
  · rewrite [if_neg hi]
    have hz : oracleHistoryTape (0 : Fin challengeDigestCard) history index = 0 := by
      unfold oracleHistoryTape
      apply List.getD_eq_default
      omega
    rewrite [hz]
    simp only [Fin.val_zero, Nat.cast_zero]

end Zcash.Snark.ZeroKnowledge
