import Zcash.Snark.ZeroKnowledge.IpaCrossTermsCost
import Zcash.Snark.ZeroKnowledge.IpaFoldReaderCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A counted real-message reader. Later rounds retain every preceding cross-term computation.
The separate materialization step must pay for every invocation of this reader. -/
def ipaCoreMessagesCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (z : F × ℕ) (U : G × ℕ) : (k : ℕ) → (Fin k → F × ℕ) →
    (Fin (2 ^ k) → F × ℕ) → (Fin (2 ^ k) → F × ℕ) →
    (Fin (2 ^ k) → G × ℕ) → Fin k → (G × G) × ℕ
  | 0, _, _, _, _ => Fin.elim0
  | k + 1, rounds, a, b, g => fun index =>
    let cross := ipaCrossTermsCosted costs groupAdd groupScale z U a b g
    Fin.cases (cross.1, cross.2 + 5) (fun j =>
      let rest := ipaCoreMessagesCosted costs groupAdd groupScale z U k
        (fun i => ((rounds i.succ).1, (rounds i.succ).2 + 1))
        (ipaFoldReaderCosted costs.add costs.multiply (ipaInverseRoundCosted costs.inverse (rounds 0)) a)
        (ipaFoldReaderCosted costs.add costs.multiply (rounds 0) b)
        (ipaFoldReaderCosted groupAdd groupScale (rounds 0) g) j
      (rest.1, cross.2 + rest.2 + 5)) index

/-- Every counted round is the original real prover message, including total inversion at zero. -/
theorem ipaCoreMessagesCosted_result (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (z : F × ℕ) (U : G × ℕ) (k : ℕ) (rounds : Fin k → F × ℕ)
    (a b : Fin (2 ^ k) → F × ℕ) (g : Fin (2 ^ k) → G × ℕ) (index : Fin k) :
    (ipaCoreMessagesCosted costs groupAdd groupScale z U k rounds a b g index).1 =
      ipaCoreMessages z.1 U.1 k (fun i => (rounds i).1)
        (fun i => (a i).1) (fun i => (b i).1) (fun i => (g i).1) index := by
  induction k with
  | zero => exact Fin.elim0 index
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) index
    · simp only [ipaCoreMessagesCosted, ipaCoreMessages, Fin.cases_zero, Fin.cons_zero,
        ipaCrossTermsCosted_result]
    · simp only [ipaCoreMessagesCosted, ipaCoreMessages, Fin.cases_succ, Fin.cons_succ, ih,
        ipaFoldReaderCosted_result, ipaInverseRoundCosted_result, foldVec]

end Zcash.Snark.ZeroKnowledge
