import Zcash.Snark.ZeroKnowledge.PlonkQuotientRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Snark

attribute [local irreducible] plonkNumeratorCoefficientsCosted

/-- Complete budget from original row readers through all eight stored quotient pieces. -/
def plonkQuotientPiecesFromRowsCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns baseRead yRead : ℕ) (key : StoredPlonkKey) : ℕ :=
  plonkNumeratorCoefficientsCostBudget costs node equal read omegaAccess actions columns baseRead yRead key +
    densePlonkQuotientPiecesCostBudget read costs.add costs.multiply omegaAccess (2 ^ 15) + 1

/-- Every constructor cost is retained; neither the numerator nor quotient is supplied as an unpriced callback. -/
theorem plonkQuotientPiecesFromRowsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (baseRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ baseRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ baseRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ baseRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ baseRead)
    (hch : Challenges.ReadBound ch baseRead) :
    (plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).2 ≤
      plonkQuotientPiecesFromRowsCostBudget costs node equal read omegaAccess actions rows.length baseRead ch.y.2 key := by
  have hn := plonkNumeratorCoefficientsCosted_cost_le costs node equal read omegaAccess key ch
    instances fixed sigma rows baseRead hinstances hfixed hsigma hrows hch
  have hq := densePlonkQuotientPiecesCosted_cost_le read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1
  rewrite [plonkNumeratorCoefficientsCosted_length] at hq
  unfold plonkQuotientPiecesFromRowsCosted
  change (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).2 +
    (densePlonkQuotientPiecesCosted read costs.add costs.multiply omegaAccess
      (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1).2 + 1 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add hn hq) 1

end Zcash.Snark.ZeroKnowledge
