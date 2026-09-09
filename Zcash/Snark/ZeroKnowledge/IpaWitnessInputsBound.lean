import Zcash.Snark.ZeroKnowledge.IpaWitnessInputsCost
import Zcash.Snark.ZeroKnowledge.IpaSimulatorCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F]

/-- Bound one fully prepared masked witness coefficient with a common original input-access price. -/
def ipaMaskedVectorReadBudget (costs : FieldOperationCosts) (equal k access : ℕ) : ℕ :=
  3 * access + sparseIpaCoefficientCostBudget costs equal k access access +
    costs.multiply + 2 * costs.add + costs.negate + equal + 4

/-- Every masked witness read pays for the actual sparse-mask computation and source coefficient. -/
theorem ipaMaskedVectorCosted_cost_le (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (access : ℕ) (hpub : pub.ReadBound access)
    (hc : ∀ i, (coefficients i).2 ≤ access) (ha : ∀ i, (alphas i).2 ≤ access)
    (index : Fin (2 ^ k)) :
    (ipaMaskedVectorCosted costs equal pub coefficients alphas index).2 ≤
      ipaMaskedVectorReadBudget costs equal k access := by
  rcases hpub with ⟨_, _, _, _, _, hp, hv, hx, _⟩
  have hm := sparseIpaCoefficientCosted_cost_le costs equal pub.point alphas access ha index
  have hb : sparseIpaCoefficientCostBudget costs equal k pub.point.2 access ≤
      sparseIpaCoefficientCostBudget costs equal k access access := by
    unfold sparseIpaCoefficientCostBudget
    gcongr
  have hi := hc index
  change (coefficients index).2 + (sparseIpaCoefficientCosted costs equal pub.point alphas index).2 +
    pub.xi.2 + pub.value.2 + costs.multiply + 2 * costs.add + costs.negate + equal + 4 ≤ _
  unfold ipaMaskedVectorReadBudget
  omega

/-- All evaluation-vector powers have the fixed vector-size bound. -/
theorem ipaEvaluationReaderCosted_cost_le (multiply : ℕ) {k : ℕ} (point : F × ℕ)
    (index : Fin (2 ^ k)) :
    (ipaEvaluationReaderCosted multiply point index).2 ≤
      2 ^ k * (multiply + 1) + point.2 + 2 := by
  have h := Nat.mul_le_mul_right (multiply + 1) index.isLt.le
  simp only [ipaEvaluationReaderCosted, fieldPowerCosted_cost]
  omega

/-- Complete actual witness-fold budget, including every total inverse and round-index adapter. -/
def ipaWitnessScalarCostBudget (costs : FieldOperationCosts) (k roundRead valueRead : ℕ) : ℕ :=
  2 ^ k * (valueRead + k * (roundRead + costs.inverse + 1 + 2 * k + costs.add + costs.multiply + 10)) + k + 1

/-- Bound the actual repeated witness fold from complete challenge and coefficient reader bounds. -/
theorem ipaWitnessScalarCosted_cost_le (costs : FieldOperationCosts) (k : ℕ)
    (rounds : Fin k → F × ℕ) (values : Fin (2 ^ k) → F × ℕ) (roundRead valueRead : ℕ)
    (hr : ∀ i, (rounds i).2 ≤ roundRead) (hv : ∀ i, (values i).2 ≤ valueRead) :
    (ipaWitnessScalarCosted costs k rounds values).2 ≤
      ipaWitnessScalarCostBudget costs k roundRead valueRead := by
  exact publicFoldCosted_cost_le costs.add costs.multiply k
    (fun i => ipaInverseRoundCosted costs.inverse (rounds i)) values
    (roundRead + costs.inverse + 1) valueRead
    (fun i => Nat.add_le_add_right (Nat.add_le_add_right (hr i) costs.inverse) 1) hv

end Zcash.Snark.ZeroKnowledge
