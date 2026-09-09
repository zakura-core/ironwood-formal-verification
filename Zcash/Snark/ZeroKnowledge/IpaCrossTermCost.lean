import Zcash.Snark.ZeroKnowledge.VectorCommitmentCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Compute one real IPA cross term, retaining both complete vector sums and public-input reads. -/
def ipaCrossTermCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {n : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin n → F × ℕ) (g : Fin n → G × ℕ) : G × ℕ :=
  let commitment := vectorCommitmentCosted groupAdd groupScale g a
  let evaluation := innerProductCosted costs.add costs.multiply a b
  (commitment.1 + (z.1 * evaluation.1) • U.1,
    commitment.2 + evaluation.2 + z.2 + U.2 + costs.multiply + groupScale + groupAdd + 3)

/-- The counted cross term has the original coefficient and evaluation-generator contributions. -/
theorem ipaCrossTermCosted_result (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {n : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin n → F × ℕ) (g : Fin n → G × ℕ) :
    (ipaCrossTermCosted costs groupAdd groupScale z U a b g).1 =
      commitGen (fun index => (g index).1) (fun index => (a index).1) +
        (z.1 * innerProduct (fun index => (a index).1) (fun index => (b index).1)) • U.1 := by
  simp only [ipaCrossTermCosted, vectorCommitmentCosted_result, innerProductCosted_result]

/-- Complete cross-term budget from explicit vector and public-input access bounds. -/
def ipaCrossTermCostBudget (costs : FieldOperationCosts)
    (groupAdd groupScale n aRead bRead gRead zRead uRead : ℕ) : ℕ :=
  (n * (aRead + gRead + groupScale + groupAdd + 2) + n * n + 1) +
    (n * (aRead + bRead + costs.multiply + costs.add + 2) + n * n + 1) +
    zRead + uRead + costs.multiply + groupScale + groupAdd + 3

/-- The actual IPA cross term fits the sum of its fully counted vector operations. -/
theorem ipaCrossTermCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {n : ℕ}
    (z : F × ℕ) (U : G × ℕ) (a b : Fin n → F × ℕ) (g : Fin n → G × ℕ)
    (aRead bRead gRead : ℕ) (ha : ∀ index, (a index).2 ≤ aRead)
    (hb : ∀ index, (b index).2 ≤ bRead) (hg : ∀ index, (g index).2 ≤ gRead) :
    (ipaCrossTermCosted costs groupAdd groupScale z U a b g).2 ≤
      ipaCrossTermCostBudget costs groupAdd groupScale n aRead bRead gRead z.2 U.2 := by
  have hc := vectorCommitmentCosted_cost_le groupAdd groupScale g a gRead aRead hg ha
  have he := innerProductCosted_cost_le costs.add costs.multiply a b aRead bRead ha hb
  change (vectorCommitmentCosted groupAdd groupScale g a).2 +
    (innerProductCosted costs.add costs.multiply a b).2 + z.2 + U.2 +
      costs.multiply + groupScale + groupAdd + 3 ≤ _
  unfold ipaCrossTermCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
