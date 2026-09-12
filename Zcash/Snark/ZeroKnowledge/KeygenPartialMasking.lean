import Zcash.Snark.ZeroKnowledge.SourcePartialMasking
import Zcash.Snark.ZeroKnowledge.KeygenExpressionMasking

/-!
# Evaluated masking certificates through expression compilation

The compiler's constant recognition and query resolution preserve partial public
values and masking certificates. The leaf premises connect the source query
valuation to the indexed fixed values supplied to the verifier's expression.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

variable {F : Type} [Field F] [DecidableEq F]

/-- The verifier expression's product evaluator uses the same absorbing-zero rule. -/
theorem exprPartialPublicValue_product (known : ℕ → Option F) (left right : Expr F) :
    exprPartialPublicValue known (.product left right) =
      partialProductValue (exprPartialPublicValue known left) (exprPartialPublicValue known right) := rfl

/-- Compilation preserves evaluated public values and every certified source mask. -/
theorem eraseExpr_partialMaskCertificates (sourceKnown : Query → Option F) (sourceSafe : Query → Bool)
    (queries : QueryState) (known : ℕ → Option F) (retained : ℕ → Bool)
    (hvalue : ∀ query, exprPartialPublicValue known
      (RichExpression.toExpr (eraseExpr (.var query) queries)) = sourceKnown query)
    (hsafe : ∀ query, sourceSafe query = true →
      exprPartialMaskInvariant known retained (RichExpression.toExpr (eraseExpr (.var query) queries)) = true)
    (expression : Expression F Query) :
    exprPartialPublicValue known (RichExpression.toExpr (eraseExpr expression queries)) =
      sourcePartialValue sourceKnown expression ∧
    (sourcePartialMaskSafe sourceKnown sourceSafe expression = true →
      exprPartialMaskInvariant known retained (RichExpression.toExpr (eraseExpr expression queries)) = true) := by
  fun_induction eraseExpr expression queries <;>
    simp_all [sourcePartialValue, sourcePartialMaskSafe, eraseExpr, RichExpression.toExpr,
      exprPartialPublicValue_product, exprPartialPublicValue, exprPartialMaskInvariant,
      partialProductValue]
  case case2 selector queries =>
    exact hvalue (.selector selector)
  case case3 column rotation queries =>
    exact ⟨hvalue (.advice column rotation), hsafe (.advice column rotation)⟩
  case case4 column rotation queries =>
    exact hvalue (.fixed column rotation)
  case case5 column rotation queries =>
    exact hvalue (.instance column rotation)
  case case6 =>
    rename_i expression queries ih
    rintro (hzero | hmask)
    · exact exprPartialMaskInvariant_of_publicValue known retained _ 0 (ih.1.trans hzero)
    · exact ih.2 hmask
  case case7 =>
    rename_i value expression queries hvalue ih
    exact Or.imp id (Or.imp id ih.2)
  case case8 =>
    rename_i expression value queries hconst ih
    exact Or.imp id (Or.imp id ih.2)
  case case9 =>
    rename_i expression value one queries hconst hone ih ihConstants
    exact Or.imp id (Or.imp id ih.2)
  case case10 =>
    rename_i expression value queries hconst ih
    constructor
    · simpa only [partialProductValue, Option.some.injEq, Option.map_some] using
        (partialProductValue_scalar_right (sourcePartialValue sourceKnown expression) value).symm
    · rintro (hzero | hconstant | hmask)
      · exact Or.inr (exprPartialMaskInvariant_of_publicValue known retained _ 0 (ih.1.trans hzero))
      · exact Or.inl hconstant
      · exact Or.inr (ih.2 hmask)
  case case12 =>
    rename_i left right queries hleft hright hrightConst ihLeft ihRight
    exact Or.imp id (Or.imp id (fun h => ⟨ihLeft.2 h.1, ihRight.2 h.2⟩))

end Zcash.Snark.ZeroKnowledge
