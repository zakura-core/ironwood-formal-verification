import Zcash.Snark.ZeroKnowledge.HonestTapeJointBound
import Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapeBound
import Zcash.Snark.ZeroKnowledge.StoredChallengePrices

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Real-prover challenge prices depend only on their actual positions, for every stored bit tape. -/
theorem storedPlonkProverTapesCosted_challenge_prices (actions read : ℕ) (bits : List Bool) :
    Challenges.readPrices (storedPlonkProverTapesCosted actions read bits).1.challenges =
      Challenges.readPrices (storedPlonkChallengePriceModel 11 read) := by
  let fields := storedFieldTapeCosted (22 + fieldSampleCount actions) read bits
  have hl : fields.1.length = 22 + fieldSampleCount actions := ofFnCosted_length _
  have hp (i : Fin 22) : (storedPlonkFieldReadCosted read fields.1 0 i.val).2 = 2 * i.val + read + 11 := by
    have hi : 0 + i.val < fields.1.length := by rewrite [hl]; have h := i.isLt; omega
    simpa only [Nat.zero_add] using storedPlonkFieldReadCosted_cost_of_lt read fields.1 0 i.val hi
  change plonkChallengesFromTape (k := 11) (fun i => (storedPlonkFieldReadCosted read fields.1 0 i.val).2) =
    plonkChallengesFromTape (fun i => 2 * i.val + read + 11)
  exact congrArg (plonkChallengesFromTape (k := 11)) (funext hp)

/-- The full real-prover budget depends on challenge prices, never on sampled challenge values. -/
theorem honestTapeJointCostBudget_congr_prices (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions tapeLength access : ℕ)
    (key : StoredPlonkKey) (left right : Challenges 11 (Fp × ℕ))
    (hprices : Challenges.readPrices left = Challenges.readPrices right) :
    honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions tapeLength access key left =
    honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions tapeLength access key right := by
  have ht : left.theta.2 = right.theta.2 := congrArg (fun p : Challenges 11 ℕ => p.theta) hprices
  have hb : left.beta.2 = right.beta.2 := congrArg (fun p : Challenges 11 ℕ => p.beta) hprices
  have hg : left.gamma.2 = right.gamma.2 := congrArg (fun p : Challenges 11 ℕ => p.gamma) hprices
  have hy : left.y.2 = right.y.2 := congrArg (fun p : Challenges 11 ℕ => p.y) hprices
  have hx : left.x.2 = right.x.2 := congrArg (fun p : Challenges 11 ℕ => p.x) hprices
  have hx1 : left.x1.2 = right.x1.2 := congrArg (fun p : Challenges 11 ℕ => p.x1) hprices
  have hx2 : left.x2.2 = right.x2.2 := congrArg (fun p : Challenges 11 ℕ => p.x2) hprices
  have hx3 : left.x3.2 = right.x3.2 := congrArg (fun p : Challenges 11 ℕ => p.x3) hprices
  have hx4 : left.x4.2 = right.x4.2 := congrArg (fun p : Challenges 11 ℕ => p.x4) hprices
  simp only [honestTapeJointCostBudget, honestStoredMaterialCostBudget, honestJointRowsCostBudget,
    ht, hb, hg, hy, hx, hx1, hx2, hx3, hx4]

end Zcash.Snark.ZeroKnowledge
