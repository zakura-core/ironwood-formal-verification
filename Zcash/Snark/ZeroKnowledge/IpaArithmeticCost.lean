import Zcash.Snark.ZeroKnowledge.PublicFoldCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaTranscript

/-!
# Counted reconstruction of the public IPA response and mask commitment

Every public input read carries its complete cost. The algorithms count both
public folds, evaluation-vector generation, the full round-message sum, and the
final field and group operations. Subtraction pays for addition and negation.
Erasure retains the existing values for all public challenge values, including
zero. Primitive prices and input-reader bounds are explicit parameters of the
structural cost model.

These results price the completed arithmetic outputs. Preparing the public
input and materializing or encoding the other transcript fields are separate
operations whose costs must be composed by the full simulator.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Explicit prices for the field and group primitives used by the IPA simulator. -/
structure IpaOperationCosts where
  fieldAdd : ℕ
  fieldMultiply : ℕ
  fieldInverse : ℕ
  fieldEqual : ℕ
  groupAdd : ℕ
  groupNegate : ℕ
  groupScale : ℕ

/-- Public IPA inputs whose accesses carry their complete supplied cost. -/
structure IpaPublicCosted (k : ℕ) (F G : Type*) where
  generators : Fin (2 ^ k) → G × ℕ
  U : G × ℕ
  W : G × ℕ
  commitment : G × ℕ
  point : F × ℕ
  value : F × ℕ
  xi : F × ℕ
  z : F × ℕ
  rounds : Fin k → F × ℕ

/-- Cost erasure retains precisely the public IPA input. -/
def IpaPublicCosted.erase {k : ℕ} {F G : Type*} (pub : IpaPublicCosted k F G) : IpaPublic k F G where
  generators := fun index => (pub.generators index).1
  U := pub.U.1
  W := pub.W.1
  commitment := pub.commitment.1
  point := pub.point.1
  value := pub.value.1
  xi := pub.xi.1
  z := pub.z.1
  rounds := fun index => (pub.rounds index).1

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Count both group terms and their addition for every public IPA round. -/
def ipaMessageSumCosted (costs : IpaOperationCosts) {k : ℕ}
    (rounds : Fin k → F × ℕ) (messages : Fin k → (G × G) × ℕ) : G × ℕ :=
  sumFinCosted costs.groupAdd fun index =>
    let round := rounds index
    let message := messages index
    (round.1⁻¹ • message.1.1 + round.1 • message.1.2,
      round.2 + message.2 + costs.fieldInverse + 2 * costs.groupScale + costs.groupAdd + 1)

/-- The counted sum has exactly the original IPA message-sum value. -/
theorem ipaMessageSumCosted_result (costs : IpaOperationCosts) {k : ℕ}
    (rounds : Fin k → F × ℕ) (messages : Fin k → (G × G) × ℕ) :
    (ipaMessageSumCosted costs rounds messages).1 =
      ipaMessageSum (fun index => (rounds index).1) (fun index => (messages index).1) := by
  rw [ipaMessageSumCosted, sumFinCosted_result]
  rfl

/-- Structural message-sum budget, including complete readers and index adapters. -/
def ipaMessageSumCostBudget (costs : IpaOperationCosts) (k roundRead messageRead : ℕ) : ℕ :=
  k * (roundRead + messageRead + costs.fieldInverse + 2 * costs.groupScale + 2 * costs.groupAdd + 2) +
    k * k + 1

/-- No round message, inversion, or scalar multiplication is omitted from the sum bound. -/
theorem ipaMessageSumCosted_cost_le (costs : IpaOperationCosts) {k : ℕ}
    (rounds : Fin k → F × ℕ) (messages : Fin k → (G × G) × ℕ)
    (roundRead messageRead : ℕ)
    (hround : ∀ index, (rounds index).2 ≤ roundRead)
    (hmessage : ∀ index, (messages index).2 ≤ messageRead) :
    (ipaMessageSumCosted costs rounds messages).2 ≤
      ipaMessageSumCostBudget costs k roundRead messageRead := by
  have hread (index : Fin k) :
      (rounds index).2 + (messages index).2 + costs.fieldInverse +
        2 * costs.groupScale + costs.groupAdd + 1 ≤
      roundRead + messageRead + costs.fieldInverse + 2 * costs.groupScale + costs.groupAdd + 1 := by
    have hr := hround index
    have hm := hmessage index
    omega
  have h := sumFinCosted_cost_le costs.groupAdd (fun index : Fin k =>
    ((rounds index).1⁻¹ • (messages index).1.1 + (rounds index).1 • (messages index).1.2,
      (rounds index).2 + (messages index).2 + costs.fieldInverse +
        2 * costs.groupScale + costs.groupAdd + 1))
    (roundRead + messageRead + costs.fieldInverse + 2 * costs.groupScale + costs.groupAdd + 1) hread
  calc
    _ ≤ k * ((roundRead + messageRead + costs.fieldInverse +
        2 * costs.groupScale + costs.groupAdd + 1) + costs.groupAdd + 1) + k * k + 1 := h
    _ = _ := by unfold ipaMessageSumCostBudget; ring

/-- Count the two public folds and the final group response. -/
def ipaPublicResponseCosted (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (scalar : F × ℕ) : G × ℕ :=
  let generators := publicFoldCosted costs.groupAdd costs.groupScale k pub.rounds pub.generators
  let powers := publicFoldCosted costs.fieldAdd costs.fieldMultiply k pub.rounds
    (fun index => fieldPowerCosted costs.fieldMultiply pub.point.1 index.val)
  (scalar.1 • generators.1 + (pub.z.1 * scalar.1 * powers.1) • pub.U.1,
    pub.point.2 + pub.z.2 + pub.U.2 + scalar.2 + generators.2 + powers.2 +
      2 * costs.fieldMultiply + 2 * costs.groupScale + costs.groupAdd + 1)

/-- Erasing both folds gives precisely the original public response. -/
theorem ipaPublicResponseCosted_result (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (scalar : F × ℕ) :
    (ipaPublicResponseCosted costs pub scalar).1 = ipaPublicResponse pub.erase scalar.1 := by
  simp only [ipaPublicResponseCosted, publicFoldCosted_result, fieldPowerCosted_result,
    ipaPublicResponse, IpaPublicCosted.erase]
  rfl

/-- Arithmetic budget for both public folds, including generation of the evaluation vector. -/
def ipaPublicResponseCostBudget (costs : IpaOperationCosts) (k roundRead generatorRead : ℕ) : ℕ :=
  (2 ^ k * (generatorRead + k * (roundRead + 2 * k + costs.groupAdd + costs.groupScale + 10)) + k + 1) +
    (2 ^ k * (2 ^ k * (costs.fieldMultiply + 1) + 1 +
      k * (roundRead + 2 * k + costs.fieldAdd + costs.fieldMultiply + 10)) + k + 1) +
    2 * costs.fieldMultiply + 2 * costs.groupScale + costs.groupAdd + 1

/-- The response budget also pays for each evaluation-vector power. -/
theorem ipaPublicResponseCosted_cost_le (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (scalar : F × ℕ) (roundRead generatorRead : ℕ)
    (hround : ∀ index, (pub.rounds index).2 ≤ roundRead)
    (hgenerator : ∀ index, (pub.generators index).2 ≤ generatorRead) :
    (ipaPublicResponseCosted costs pub scalar).2 ≤
      pub.point.2 + pub.z.2 + pub.U.2 + scalar.2 +
        ipaPublicResponseCostBudget costs k roundRead generatorRead := by
  have hg := publicFoldCosted_cost_le costs.groupAdd costs.groupScale k pub.rounds pub.generators
    roundRead generatorRead hround hgenerator
  have hp (index : Fin (2 ^ k)) :
      (fieldPowerCosted costs.fieldMultiply pub.point.1 index.val).2 ≤
        2 ^ k * (costs.fieldMultiply + 1) + 1 := by
    rw [fieldPowerCosted_cost]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ index.isLt.le) 1
  have hf := publicFoldCosted_cost_le costs.fieldAdd costs.fieldMultiply k pub.rounds
    (fun index => fieldPowerCosted costs.fieldMultiply pub.point.1 index.val)
    roundRead (2 ^ k * (costs.fieldMultiply + 1) + 1) hround hp
  dsimp only [ipaPublicResponseCosted, ipaPublicResponseCostBudget]
  omega

/-- Reconstruct the mask commitment while retaining all arithmetic and input-read costs. -/
def completeIpaMaskCosted (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (messages : Fin k → (G × G) × ℕ)
    (scalar blind : F × ℕ) : G × ℕ :=
  let response := ipaPublicResponseCosted costs pub scalar
  let messageSum := ipaMessageSumCosted costs pub.rounds messages
  let generatorZero := pub.generators 0
  (pub.xi.1⁻¹ • (response.1 + blind.1 • pub.W.1 -
      (pub.commitment.1 - pub.value.1 • generatorZero.1 + messageSum.1)),
    response.2 + messageSum.2 + pub.xi.2 + pub.W.2 + pub.commitment.2 + pub.value.2 +
      generatorZero.2 + blind.2 + costs.fieldInverse + 3 * costs.groupScale +
      4 * costs.groupAdd + 2 * costs.groupNegate + 1)

/-- Cost erasure preserves the completed mask commitment, even when the public challenge is zero. -/
theorem completeIpaMaskCosted_result (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (messages : Fin k → (G × G) × ℕ)
    (scalar blind : F × ℕ) :
    (completeIpaMaskCosted costs pub messages scalar blind).1 =
      (completeIpaTranscript pub.erase (fun index => (messages index).1) scalar.1 blind.1).maskCommitment := by
  simp only [completeIpaMaskCosted, ipaPublicResponseCosted_result, ipaMessageSumCosted_result,
    completeIpaTranscript, IpaPublicCosted.erase]

/-- Arithmetic budget for reconstructing the complete IPA mask commitment. -/
def completeIpaMaskCostBudget (costs : IpaOperationCosts) (k roundRead generatorRead messageRead : ℕ) : ℕ :=
  ipaPublicResponseCostBudget costs k roundRead generatorRead +
    ipaMessageSumCostBudget costs k roundRead messageRead +
    costs.fieldInverse + 3 * costs.groupScale + 4 * costs.groupAdd + 2 * costs.groupNegate + 1

/-- The mask reconstruction bound composes both folds and all round-message work. -/
theorem completeIpaMaskCosted_cost_le (costs : IpaOperationCosts) {k : ℕ}
    (pub : IpaPublicCosted k F G) (messages : Fin k → (G × G) × ℕ)
    (scalar blind : F × ℕ) (roundRead generatorRead messageRead : ℕ)
    (hround : ∀ index, (pub.rounds index).2 ≤ roundRead)
    (hgenerator : ∀ index, (pub.generators index).2 ≤ generatorRead)
    (hmessage : ∀ index, (messages index).2 ≤ messageRead) :
    (completeIpaMaskCosted costs pub messages scalar blind).2 ≤
      pub.point.2 + pub.z.2 + pub.U.2 + scalar.2 + pub.xi.2 + pub.W.2 + pub.commitment.2 +
        pub.value.2 + (pub.generators 0).2 + blind.2 +
        completeIpaMaskCostBudget costs k roundRead generatorRead messageRead := by
  have hr := ipaPublicResponseCosted_cost_le costs pub scalar roundRead generatorRead hround hgenerator
  have hm := ipaMessageSumCosted_cost_le costs pub.rounds messages roundRead messageRead hround hmessage
  dsimp only [completeIpaMaskCosted, completeIpaMaskCostBudget]
  omega

end Zcash.Snark.ZeroKnowledge
