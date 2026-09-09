import Zcash.Snark.ZeroKnowledge.PlonkNumeratorCoefficientsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark

/-- Complete actual-numerator budget in the Action count, stored key sizes, and priced input readers. -/
def plonkNumeratorCoefficientsCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns baseRead yRead : ℕ) (key : StoredPlonkKey) : ℕ :=
  cosetCoefficientsCostBudget costs read omegaAccess 15 omegaAccess
    (plonkNumeratorSampleCostBudget costs node equal read omegaAccess actions columns baseRead yRead key)

/-- The entire original numerator is computed within the stated bound, with no unpriced polynomial callback. -/
theorem plonkNumeratorCoefficientsCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (baseRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ baseRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ baseRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ baseRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ baseRead)
    (hch : Challenges.ReadBound ch baseRead) :
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).2 ≤
      plonkNumeratorCoefficientsCostBudget costs node equal read omegaAccess actions rows.length baseRead ch.y.2 key := by
  exact cosetCoefficientsCosted_cost_le costs read omegaAccess 15 (omegaOf 16, omegaAccess)
    (plonkNumeratorSampleCosted costs node equal read omegaAccess key ch instances fixed sigma rows)
    (plonkNumeratorSampleCostBudget costs node equal read omegaAccess actions rows.length baseRead ch.y.2 key)
    (fun index => plonkNumeratorSampleCosted_cost_le costs node equal read omegaAccess key ch
      instances fixed sigma rows index baseRead hinstances hfixed hsigma hrows hch)

end Zcash.Snark.ZeroKnowledge
