import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.IpaProver

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*} [Field F]

/-- Accumulate the real incoming blind, sparse-mask blind, and every left/right blind. -/
def ipaFinalBlindCosted (costs : FieldOperationCosts) {k : ℕ} (rho xi mask : F × ℕ)
    (rounds : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) : F × ℕ :=
  let total := sumFinCosted costs.add fun i =>
    let round := rounds i
    let blind := blinds i
    (round.1⁻¹ * blind.1.1 + round.1 * blind.1.2,
      round.2 + blind.2 + costs.inverse + 2 * costs.multiply + costs.add + 1)
  (rho.1 + xi.1 * mask.1 + total.1,
    rho.2 + xi.2 + mask.2 + total.2 + costs.multiply + 2 * costs.add + 2)

/-- Erasure is the exact aggregate blind of the original IPA prover, including zero challenges. -/
theorem ipaFinalBlindCosted_result (costs : FieldOperationCosts) {k : ℕ} (rho xi mask : F × ℕ)
    (rounds : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) :
    (ipaFinalBlindCosted costs rho xi mask rounds blinds).1 =
      ipaFinalBlind rho.1 xi.1 (fun i => (rounds i).1) (mask.1, fun i => (blinds i).1) := by
  simp only [ipaFinalBlindCosted, sumFinCosted_result, ipaFinalBlind]

/-- Complete aggregate-blind budget from explicit input and reader prices. -/
def ipaFinalBlindCostBudget (costs : FieldOperationCosts)
    (k rhoRead xiRead maskRead roundRead blindRead : ℕ) : ℕ :=
  rhoRead + xiRead + maskRead +
    (k * (roundRead + blindRead + costs.inverse + 2 * costs.multiply + 2 * costs.add + 2) + k * k + 1) +
    costs.multiply + 2 * costs.add + 2

/-- Every read and arithmetic operation of the original final blind is bounded. -/
theorem ipaFinalBlindCosted_cost_le (costs : FieldOperationCosts) {k : ℕ} (rho xi mask : F × ℕ)
    (rounds : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) (roundRead blindRead : ℕ)
    (hr : ∀ i, (rounds i).2 ≤ roundRead) (hb : ∀ i, (blinds i).2 ≤ blindRead) :
    (ipaFinalBlindCosted costs rho xi mask rounds blinds).2 ≤
      ipaFinalBlindCostBudget costs k rho.2 xi.2 mask.2 roundRead blindRead := by
  have h := sumFinCosted_cost_le costs.add (fun i : Fin k =>
    ((rounds i).1⁻¹ * (blinds i).1.1 + (rounds i).1 * (blinds i).1.2,
      (rounds i).2 + (blinds i).2 + costs.inverse + 2 * costs.multiply + costs.add + 1))
    (roundRead + blindRead + costs.inverse + 2 * costs.multiply + costs.add + 1) (by
      intro i
      have ha := hr i
      have hh := hb i
      dsimp only
      omega)
  change rho.2 + xi.2 + mask.2 + (sumFinCosted costs.add _).2 +
    costs.multiply + 2 * costs.add + 2 ≤ _
  unfold ipaFinalBlindCostBudget
  convert Nat.add_le_add_right (Nat.add_le_add_left h (rho.2 + xi.2 + mask.2))
    (costs.multiply + 2 * costs.add + 2) using 1 <;> ring

end Zcash.Snark.ZeroKnowledge
