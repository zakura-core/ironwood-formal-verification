import Zcash.Snark.ZeroKnowledge.ChallengeReadCost
import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost
import Zcash.Snark.ZeroKnowledge.PlonkAttempt

/-! # Complete construction and checking of the original received-challenge schedule -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Materialize all named and round challenges, retaining every complete scalar producer. -/
def plonkChallengeSequenceCosted {k : ℕ} (ch : Challenges k (Fp × ℕ)) : List Fp × ℕ :=
  let named := ([ch.theta.1, ch.beta.1, ch.gamma.1, ch.y.1, ch.x.1, ch.x1.1,
    ch.x2.1, ch.x3.1, ch.x4.1, ch.xi.1, ch.z.1],
    ch.theta.2 + ch.beta.2 + ch.gamma.2 + ch.y.2 + ch.x.2 + ch.x1.2 +
      ch.x2.2 + ch.x3.2 + ch.x4.2 + ch.xi.2 + ch.z.2 + 12)
  appendProducedCosted named (ofFnCosted ch.ipaRound)

/-- Every received challenge stays in its original schedule position. -/
theorem plonkChallengeSequenceCosted_result {k : ℕ} (ch : Challenges k (Fp × ℕ)) :
    (plonkChallengeSequenceCosted ch).1 = plonkChallengeSequence (Challenges.eraseCosts ch) := by
  simp only [plonkChallengeSequenceCosted, appendProducedCosted_result, ofFnCosted_result,
    plonkChallengeSequence, Challenges.eraseCosts]

/-- The produced challenge tape has exactly the original eleven plus round slots. -/
theorem plonkChallengeSequenceCosted_length {k : ℕ} (ch : Challenges k (Fp × ℕ)) :
    (plonkChallengeSequenceCosted ch).1.length = 11 + k := by
  rw [plonkChallengeSequenceCosted_result]
  exact plonkChallengeSequence_length _

/-- Challenge construction includes all named fields, round collection, and prefix copying. -/
theorem plonkChallengeSequenceCosted_cost_le {k : ℕ} (ch : Challenges k (Fp × ℕ))
    (access : ℕ) (hread : Challenges.ReadBound ch access) :
    (plonkChallengeSequenceCosted ch).2 ≤ (11 + k) * (access + 2) + k * k + 15 := by
  rcases hread with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hround⟩
  have hr := ofFnCosted_cost_le ch.ipaRound access hround
  simp only [plonkChallengeSequenceCosted, appendProducedCosted_cost,
    List.length_cons, List.length_nil]
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hr]

/-- Check precisely the original opening and round failures, with complete read costs. -/
def afterStoredChallengeCosted (equal read : ℕ) (x : Fp × ℕ) (sequence : List Fp)
    (index : ℕ) : Option ProverAttemptFailure × ℕ :=
  if index = 6 ∧ x.1 = 0 then
    (some .coincidentOpeningQueries, x.2 + equal + 5)
  else
    let value := getDListCosted read (0 : Fp) sequence index
    let status := if 11 ≤ index ∧ value.1 = 0 then some .retryRandomness else none
    (status, x.2 + value.2 + 2 * equal + 10)

/-- Stored checking preserves the exact original post-challenge policy at every index. -/
theorem afterStoredChallengeCosted_result (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (index : ℕ) :
    (afterStoredChallengeCosted equal read ch.x (plonkChallengeSequence (Challenges.eraseCosts ch)) index).1 =
      plonkAfterChallenge (Challenges.eraseCosts ch) index := by
  by_cases h : index = 6 ∧ ch.x.1 = 0 <;>
    simp [afterStoredChallengeCosted, plonkAfterChallenge, Challenges.eraseCosts,
      plonkAttemptChallenge, getDListCosted_result, h]

/-- Both field checks and the entire stored challenge lookup remain in the bound. -/
theorem afterStoredChallengeCosted_cost_le (equal read : ℕ) (x : Fp × ℕ)
    (sequence : List Fp) (index : ℕ) :
    (afterStoredChallengeCosted equal read x sequence index).2 ≤
      x.2 + 2 * sequence.length + read + 2 * equal + 11 := by
  have hread := getDListCosted_cost_le read (0 : Fp) sequence index
  by_cases h : index = 6 ∧ x.1 = 0
  · simp only [afterStoredChallengeCosted, if_pos h]
    omega
  · simp only [afterStoredChallengeCosted, if_neg h]
    omega

end Zcash.Snark.ZeroKnowledge
