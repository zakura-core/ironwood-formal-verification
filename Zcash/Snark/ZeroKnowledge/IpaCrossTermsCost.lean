import Zcash.Snark.ZeroKnowledge.IpaCrossTermCost
import Zcash.Snark.ZeroKnowledge.PublicFoldCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Both original cross terms with all half-vector adapters and reads counted. -/
def ipaCrossTermsCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {k : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin (2 ^ (k + 1)) → F × ℕ)
    (g : Fin (2 ^ (k + 1)) → G × ℕ) : (G × G) × ℕ :=
  let left := ipaCrossTermCosted costs groupAdd groupScale z U
    (hiHalfCosted a) (loHalfCosted b) (loHalfCosted g)
  let right := ipaCrossTermCosted costs groupAdd groupScale z U
    (loHalfCosted a) (hiHalfCosted b) (hiHalfCosted g)
  ((left.1, right.1), left.2 + right.2 + 1)

/-- Erasure retains the exact two source cross terms, with no challenge restriction. -/
theorem ipaCrossTermsCosted_result (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {k : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin (2 ^ (k + 1)) → F × ℕ)
    (g : Fin (2 ^ (k + 1)) → G × ℕ) :
    (ipaCrossTermsCosted costs groupAdd groupScale z U a b g).1 =
      ipaCrossTerms z.1 U.1 (fun i => (a i).1) (fun i => (b i).1) (fun i => (g i).1) := by
  simp only [ipaCrossTermsCosted, ipaCrossTermCosted_result, hiHalfCosted_result,
    loHalfCosted_result, ipaCrossTerms]

/-- A common vector-read bound includes the upper-half dimension computation. -/
def ipaCrossTermsCostBudget (costs : FieldOperationCosts)
    (groupAdd groupScale k valueRead zRead uRead : ℕ) : ℕ :=
  2 * ipaCrossTermCostBudget costs groupAdd groupScale (2 ^ k)
    (valueRead + 2 * k + 3) (valueRead + 2 * k + 3) (valueRead + 2 * k + 3) zRead uRead + 1

/-- Complete pair cost, including both original inner products and commitments. -/
theorem ipaCrossTermsCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {k : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin (2 ^ (k + 1)) → F × ℕ)
    (g : Fin (2 ^ (k + 1)) → G × ℕ) (valueRead : ℕ)
    (ha : ∀ i, (a i).2 ≤ valueRead) (hb : ∀ i, (b i).2 ≤ valueRead)
    (hg : ∀ i, (g i).2 ≤ valueRead) :
    (ipaCrossTermsCosted costs groupAdd groupScale z U a b g).2 ≤
      ipaCrossTermsCostBudget costs groupAdd groupScale k valueRead z.2 U.2 := by
  have hl := ipaCrossTermCosted_cost_le costs groupAdd groupScale z U
    (hiHalfCosted a) (loHalfCosted b) (loHalfCosted g)
    (valueRead + 2 * k + 3) (valueRead + 2 * k + 3) (valueRead + 2 * k + 3)
    (hiHalfCosted_cost_le a valueRead ha) (fun i => by have h := loHalfCosted_cost_le b valueRead hb i; omega) (fun i => by have h := loHalfCosted_cost_le g valueRead hg i; omega)
  have hr := ipaCrossTermCosted_cost_le costs groupAdd groupScale z U
    (loHalfCosted a) (hiHalfCosted b) (hiHalfCosted g)
    (valueRead + 2 * k + 3) (valueRead + 2 * k + 3) (valueRead + 2 * k + 3)
    (fun i => by have h := loHalfCosted_cost_le a valueRead ha i; omega) (hiHalfCosted_cost_le b valueRead hb) (hiHalfCosted_cost_le g valueRead hg)
  change (ipaCrossTermCosted costs groupAdd groupScale z U
    (hiHalfCosted a) (loHalfCosted b) (loHalfCosted g)).2 +
      (ipaCrossTermCosted costs groupAdd groupScale z U
        (loHalfCosted a) (hiHalfCosted b) (hiHalfCosted g)).2 + 1 ≤ _
  unfold ipaCrossTermsCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
