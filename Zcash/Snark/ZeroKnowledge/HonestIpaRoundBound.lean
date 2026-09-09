import Zcash.Snark.ZeroKnowledge.HonestIpaCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A common price for actual masked coefficients, evaluation powers, and generators. -/
def honestIpaVectorReadBudget (costs : FieldOperationCosts) (equal k access : ℕ) : ℕ :=
  ipaMaskedVectorReadBudget costs equal k access +
    (2 ^ k * (costs.multiply + 1) + access + 2) + access

/-- Complete original core-message budget after preparing the actual three input vectors. -/
def honestIpaCoreCostBudget (costs : FieldOperationCosts) (groupAdd groupScale equal k access : ℕ) : ℕ :=
  ipaCoreMessagesCostBudget costs groupAdd groupScale access access k access
    (honestIpaVectorReadBudget costs equal k access)

/-- Bound each full real core computation from original public inputs, coefficients, and sparse coins. -/
theorem honestIpaCoreCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (access : ℕ) (hpub : pub.ReadBound access)
    (hc : ∀ i, (coefficients i).2 ≤ access) (ha : ∀ i, (alphas i).2 ≤ access) (index : Fin k) :
    (ipaCoreMessagesCosted costs groupAdd groupScale pub.z pub.U k pub.rounds
      (ipaMaskedVectorCosted costs equal pub coefficients alphas)
      (ipaEvaluationReaderCosted costs.multiply pub.point) pub.generators index).2 ≤
      honestIpaCoreCostBudget costs groupAdd groupScale equal k access := by
  have hm := ipaMaskedVectorCosted_cost_le costs equal pub coefficients alphas access hpub hc ha
  rcases hpub with ⟨hg, hr, hU, _, _, hp, _, _, hz⟩
  have hma (i : Fin (2 ^ k)) :
      (ipaMaskedVectorCosted costs equal pub coefficients alphas i).2 ≤
        honestIpaVectorReadBudget costs equal k access := by
    have h := hm i
    unfold honestIpaVectorReadBudget
    omega
  have heb (i : Fin (2 ^ k)) :
      (ipaEvaluationReaderCosted costs.multiply pub.point i).2 ≤
        honestIpaVectorReadBudget costs equal k access := by
    have h := ipaEvaluationReaderCosted_cost_le costs.multiply pub.point i
    unfold honestIpaVectorReadBudget
    omega
  have hgg (i : Fin (2 ^ k)) : (pub.generators i).2 ≤ honestIpaVectorReadBudget costs equal k access := by
    have h := hg i
    unfold honestIpaVectorReadBudget
    omega
  have h := ipaCoreMessagesCosted_cost_le costs groupAdd groupScale pub.z pub.U k pub.rounds
    (ipaMaskedVectorCosted costs equal pub coefficients alphas)
    (ipaEvaluationReaderCosted costs.multiply pub.point) pub.generators access
    (honestIpaVectorReadBudget costs equal k access) hr hma heb hgg index
  exact h.trans (ipaCoreMessagesCostBudget_mono costs groupAdd groupScale k hz hU le_rfl le_rfl)

/-- Original message work plus actual left/right blind reads and group operations. -/
def honestIpaRoundCostBudget (costs : FieldOperationCosts) (groupAdd groupScale equal k access : ℕ) : ℕ :=
  honestIpaCoreCostBudget costs groupAdd groupScale equal k access + 2 * access + groupAdd + groupScale + 1

/-- Both emitted points retain their complete real core and independent blind costs. -/
theorem honestIpaRoundCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) (access : ℕ)
    (hpub : pub.ReadBound access) (hc : ∀ i, (coefficients i).2 ≤ access)
    (ha : ∀ i, (alphas i).2 ≤ access) (hb : ∀ i, (blinds i).2 ≤ access) (index : Fin k) :
    (honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds index).1.2 ≤
        honestIpaRoundCostBudget costs groupAdd groupScale equal k access ∧
      (honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds index).2.2 ≤
        honestIpaRoundCostBudget costs groupAdd groupScale equal k access := by
  have h := honestIpaCoreCosted_cost_le costs groupAdd groupScale equal pub coefficients alphas access hpub hc ha index
  have hW := hpub.2.2.2.1
  have hb' := hb index
  simp only [honestIpaRoundCosted, honestIpaRoundCostBudget]
  constructor <;> omega

end Zcash.Snark.ZeroKnowledge
