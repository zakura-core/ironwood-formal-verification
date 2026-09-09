import Zcash.Snark.ZeroKnowledge.SparseIpaCoefficientCost
import Zcash.Snark.ZeroKnowledge.IpaArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaFoldReaderCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F]

/-- Actual masked witness coefficient; the claimed value remains the original supplied input. -/
def ipaMaskedVectorCosted (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (index : Fin (2 ^ k)) : F × ℕ :=
  let coefficient := coefficients index
  let mask := sparseIpaCoefficientCosted costs equal pub.point alphas index
  (coefficient.1 + pub.xi.1 * mask.1 - (if index.val = 0 then pub.value.1 else 0),
    coefficient.2 + mask.2 + pub.xi.2 + pub.value.2 + costs.multiply +
      2 * costs.add + costs.negate + equal + 4)

/-- Erasure agrees with the original masked witness on every claimed evaluation. -/
theorem ipaMaskedVectorCosted_result (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (index : Fin (2 ^ k)) :
    (ipaMaskedVectorCosted costs equal pub coefficients alphas index).1 =
      ipaMaskedVector pub.erase (fun i => (coefficients i).1) (fun i => (alphas i).1) index := by
  simp only [ipaMaskedVectorCosted, sparseIpaCoefficientCosted_result, ipaMaskedVector,
    IpaPublicCosted.erase, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Fin.ext_iff]
  split_ifs <;> simp_all

/-- Generate one original evaluation-vector entry with its complete point and exponentiation cost. -/
def ipaEvaluationReaderCosted (multiply : ℕ) {k : ℕ} (point : F × ℕ)
    (index : Fin (2 ^ k)) : F × ℕ :=
  let power := fieldPowerCosted multiply point.1 index.val
  (power.1, power.2 + point.2 + 1)

/-- The evaluation reader produces the original public power vector. -/
theorem ipaEvaluationReaderCosted_result (multiply : ℕ) {k : ℕ} (point : F × ℕ)
    (index : Fin (2 ^ k)) :
    (ipaEvaluationReaderCosted multiply point index).1 = evalVector k point.1 index := by
  simp only [ipaEvaluationReaderCosted, fieldPowerCosted_result, evalVector]

/-- Inverting the public-fold challenges gives the original witness fold, including zero values. -/
theorem publicFold_inverse_rounds (k : ℕ) (rounds : Fin k → F) (values : Fin (2 ^ k) → F) :
    publicFold k (fun i => (rounds i)⁻¹) values = foldByRounds k rounds values := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [publicFold, foldByRounds, foldVec] using
      (ih (fun i => rounds i.succ) (loHalf values + (rounds 0)⁻¹ • hiHalf values))

/-- Run the actual coefficient fold with a counted inverse challenge reader. -/
def ipaWitnessScalarCosted (costs : FieldOperationCosts) (k : ℕ)
    (rounds : Fin k → F × ℕ) (values : Fin (2 ^ k) → F × ℕ) : F × ℕ :=
  publicFoldCosted costs.add costs.multiply k
    (fun i => ipaInverseRoundCosted costs.inverse (rounds i)) values

/-- The counted scalar is precisely the repeated inverse witness fold. -/
theorem ipaWitnessScalarCosted_result (costs : FieldOperationCosts) (k : ℕ)
    (rounds : Fin k → F × ℕ) (values : Fin (2 ^ k) → F × ℕ) :
    (ipaWitnessScalarCosted costs k rounds values).1 =
      foldByRounds k (fun i => (rounds i).1) (fun i => (values i).1) := by
  simp only [ipaWitnessScalarCosted, publicFoldCosted_result,
    ipaInverseRoundCosted_result, publicFold_inverse_rounds]

end Zcash.Snark.ZeroKnowledge
