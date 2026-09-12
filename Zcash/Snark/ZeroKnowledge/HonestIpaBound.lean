import Zcash.Snark.ZeroKnowledge.HonestIpaRoundBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Complete sparse-mask commitment budget, including every coefficient and generator read. -/
def honestIpaMaskCostBudget (costs : FieldOperationCosts) (groupAdd groupScale equal k access : ℕ) : ℕ :=
  (2 ^ k * (sparseIpaCoefficientCostBudget costs equal k access access + access + groupScale + groupAdd + 2) +
    2 ^ k * 2 ^ k + 1) + 2 * access + groupAdd + groupScale + 1

/-- Full finite transcript budget for the actual honest IPA, including every round and both final responses. -/
def honestIpaTranscriptCostBudget (costs : FieldOperationCosts) (groupAdd groupScale equal k access : ℕ) : ℕ :=
  k * (2 * honestIpaRoundCostBudget costs groupAdd groupScale equal k access + 2) + k * k +
    honestIpaMaskCostBudget costs groupAdd groupScale equal k access +
    ipaWitnessScalarCostBudget costs k access (ipaMaskedVectorReadBudget costs equal k access) +
    ipaFinalBlindCostBudget costs k access access access access access + 2

/-- The fully materialized real IPA fits the derived budget on every input and challenge. -/
theorem materializedHonestIpaCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (alphas : Fin k → F × ℕ) (mask : F × ℕ)
    (blinds : Fin k → (F × F) × ℕ) (access : ℕ) (hpub : pub.ReadBound access)
    (hc : ∀ i, (coefficients i).2 ≤ access) (hrho : rho.2 ≤ access)
    (ha : ∀ i, (alphas i).2 ≤ access) (hmask : mask.2 ≤ access)
    (hb : ∀ i, (blinds i).2 ≤ access) :
    (materializeIpaCosted (honestIpaTranscriptCosted costs groupAdd groupScale equal
      pub coefficients rho alphas mask blinds)).2 ≤
      honestIpaTranscriptCostBudget costs groupAdd groupScale equal k access := by
  have hmasked := ipaMaskedVectorCosted_cost_le costs equal pub coefficients alphas access hpub hc ha
  have hmessages := honestIpaRoundCosted_cost_le costs groupAdd groupScale equal pub coefficients alphas blinds
    access hpub hc ha hb
  rcases hpub with ⟨hg, hr, _, hW, _, hp, _, hx, _⟩
  have hsparse (i : Fin (2 ^ k)) :
      (sparseIpaCoefficientCosted costs equal pub.point alphas i).2 ≤
        sparseIpaCoefficientCostBudget costs equal k access access := by
    have h := sparseIpaCoefficientCosted_cost_le costs equal pub.point alphas access ha i
    refine h.trans ?_
    unfold sparseIpaCoefficientCostBudget
    gcongr
  have hcommit := vectorCommitmentCosted_cost_le groupAdd groupScale pub.generators
    (sparseIpaCoefficientCosted costs equal pub.point alphas) access
    (sparseIpaCoefficientCostBudget costs equal k access access) hg hsparse
  have hmaskBound :
      (honestIpaTranscriptCosted costs groupAdd groupScale equal pub coefficients rho alphas mask blinds).maskCommitment.2 ≤
        honestIpaMaskCostBudget costs groupAdd groupScale equal k access := by
    change (vectorCommitmentCosted groupAdd groupScale pub.generators
      (sparseIpaCoefficientCosted costs equal pub.point alphas)).2 +
        mask.2 + pub.W.2 + groupAdd + groupScale + 1 ≤ _
    unfold honestIpaMaskCostBudget
    omega
  have hscalar := ipaWitnessScalarCosted_cost_le costs k pub.rounds
    (ipaMaskedVectorCosted costs equal pub coefficients alphas) access
    (ipaMaskedVectorReadBudget costs equal k access) hr hmasked
  have hblind : (ipaFinalBlindCosted costs rho pub.xi mask pub.rounds blinds).2 ≤
      ipaFinalBlindCostBudget costs k access access access access access := by
    have h := ipaFinalBlindCosted_cost_le costs rho pub.xi mask pub.rounds blinds access access hr hb
    refine h.trans ?_
    unfold ipaFinalBlindCostBudget
    gcongr
  exact materializeIpaCosted_cost_le
    (honestIpaTranscriptCosted costs groupAdd groupScale equal pub coefficients rho alphas mask blinds)
    (honestIpaMaskCostBudget costs groupAdd groupScale equal k access)
    (honestIpaRoundCostBudget costs groupAdd groupScale equal k access)
    (ipaWitnessScalarCostBudget costs k access (ipaMaskedVectorReadBudget costs equal k access))
    (ipaFinalBlindCostBudget costs k access access access access access)
    hmaskBound hmessages hscalar hblind

end Zcash.Snark.ZeroKnowledge
