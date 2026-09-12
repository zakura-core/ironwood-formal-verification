import Zcash.Snark.ZeroKnowledge.PublicFoldCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- One entry of the next IPA vector, counting both half reads and the challenge. -/
def ipaFoldReaderCosted (add scale : ℕ) {k : ℕ} (challenge : F × ℕ)
    (values : Fin (2 ^ (k + 1)) → G × ℕ) (index : Fin (2 ^ k)) : G × ℕ :=
  let low := loHalfCosted values index
  let high := hiHalfCosted values index
  (low.1 + challenge.1 • high.1, low.2 + high.2 + challenge.2 + add + scale + 1)

/-- The counted reader is the source's low/high vector update. -/
theorem ipaFoldReaderCosted_result (add scale : ℕ) {k : ℕ} (challenge : F × ℕ)
    (values : Fin (2 ^ (k + 1)) → G × ℕ) (index : Fin (2 ^ k)) :
    (ipaFoldReaderCosted add scale challenge values index).1 =
      (loHalf (fun i => (values i).1) + challenge.1 • hiHalf (fun i => (values i).1)) index := by
  simp only [ipaFoldReaderCosted, loHalfCosted_result, hiHalfCosted_result,
    Pi.add_apply, Pi.smul_apply]

/-- The next reader retains the complete cost of both original reads. -/
theorem ipaFoldReaderCosted_cost_le (add scale : ℕ) {k : ℕ} (challenge : F × ℕ)
    (values : Fin (2 ^ (k + 1)) → G × ℕ) (valueRead : ℕ)
    (hvalue : ∀ i, (values i).2 ≤ valueRead) (index : Fin (2 ^ k)) :
    (ipaFoldReaderCosted add scale challenge values index).2 ≤
      2 * valueRead + challenge.2 + add + scale + 2 * k + 5 := by
  have hl := loHalfCosted_cost_le values valueRead hvalue index
  have hh := hiHalfCosted_cost_le values valueRead hvalue index
  change (loHalfCosted values index).2 + (hiHalfCosted values index).2 +
    challenge.2 + add + scale + 1 ≤ _
  omega

/-- Inverting a round challenge retains its access cost, including at zero. -/
def ipaInverseRoundCosted (inverse : ℕ) (round : F × ℕ) : F × ℕ :=
  (round.1⁻¹, round.2 + inverse + 1)

/-- Erasure performs exactly the source's total inversion. -/
theorem ipaInverseRoundCosted_result (inverse : ℕ) (round : F × ℕ) :
    (ipaInverseRoundCosted inverse round).1 = round.1⁻¹ := rfl

/-- Exact cost of the inverse-round adapter. -/
theorem ipaInverseRoundCosted_cost (inverse : ℕ) (round : F × ℕ) :
    (ipaInverseRoundCosted inverse round).2 = round.2 + inverse + 1 := rfl

end Zcash.Snark.ZeroKnowledge
