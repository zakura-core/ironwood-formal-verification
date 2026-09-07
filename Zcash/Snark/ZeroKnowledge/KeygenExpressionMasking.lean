import Zcash.Snark.ZeroKnowledge.SourceExpressionMasking
import Zcash.Snark.ZeroKnowledge.PartialExpressionMasking
import Zcash.Snark.ZeroKnowledge.KeygenExpressionDegree

/-!
# Masking certificates through expression compilation

Query resolution and the compiler's product, negation, and scaling cases preserve
the structural zero and mask-safety certificates. Their hypotheses concern only
individual query leaves and public fixed values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Expression compilation is independent of the implementation of field equality decisions. -/
theorem eraseExpr_decidableEq_irrel (left right : DecidableEq F)
    (expression : Expression F Query) (queries : QueryState) :
    @eraseExpr F (inferInstance : Field F) left expression queries =
      @eraseExpr F (inferInstance : Field F) right expression queries :=
  congrArg (fun equality : DecidableEq F => @eraseExpr F (inferInstance : Field F) equality expression queries)
    (Subsingleton.elim left right)

omit [DecidableEq F] in
/-- The entire pinned constraint-system projection is independent of the field equality decider. -/
theorem derivePinnedCS_decidableEq_irrel (left right : DecidableEq F)
    (system : ConstraintSystem F) (map : SelCompressMap) :
    @PinnedConstraintSystem.derive F (inferInstance : Field F) left system map =
      @PinnedConstraintSystem.derive F (inferInstance : Field F) right system map :=
  congrArg (fun equality : DecidableEq F =>
    @PinnedConstraintSystem.derive F (inferInstance : Field F) equality system map) (Subsingleton.elim left right)

/-- Source zero and mask-safety certificates survive query resolution and verifier-expression translation. -/
theorem eraseExpr_sourceMaskCertificates (zero safe : Query → Bool) (queries : QueryState)
    (known : ℕ → Option F) (retained : ℕ → Bool)
    (hzero : ∀ query, zero query = true →
      exprPartialPublicValue known (RichExpression.toExpr (eraseExpr (.var query) queries)) = some 0)
    (hsafe : ∀ query, safe query = true →
      exprPartialMaskInvariant known retained (RichExpression.toExpr (eraseExpr (.var query) queries)) = true)
    (expression : Expression F Query) :
    (sourceExpressionZero zero expression = true →
      exprPartialPublicValue known (RichExpression.toExpr (eraseExpr expression queries)) = some 0) ∧
    (sourceExpressionMaskSafe zero safe expression = true →
      exprPartialMaskInvariant known retained (RichExpression.toExpr (eraseExpr expression queries)) = true) := by
  fun_induction eraseExpr expression queries <;>
    simp_all [sourceExpressionZero, sourceExpressionMaskSafe, eraseExpr, RichExpression.toExpr,
      exprPartialPublicValue, exprPartialMaskInvariant]
  case case3 column rotation queries =>
    simpa [eraseExpr, RichExpression.toExpr, exprPartialPublicValue, exprPartialMaskInvariant] using
      And.intro (hzero (.advice column rotation)) (hsafe (.advice column rotation))
  case case4 column rotation queries =>
    simpa [eraseExpr, RichExpression.toExpr, exprPartialPublicValue] using hzero (.fixed column rotation)
  case case5 column rotation queries =>
    simpa [eraseExpr, RichExpression.toExpr, exprPartialPublicValue] using hzero (.instance column rotation)
  case case6 =>
    rename_i expression queries ih
    rintro (hzero | hsafe)
    · exact exprPartialMaskInvariant_of_publicValue known retained _ 0 (ih.1 hzero)
    · exact ih.2 hsafe
  case case7 =>
    rename_i value expression queries hvalue ih
    rintro (hzero | hsafe)
    · exact Or.inr (Or.inl (ih.1 hzero))
    · exact Or.inr (Or.inr (ih.2 hsafe))
  case case8 =>
    rename_i expression value queries hconst ih
    rintro (hzero | hsafe)
    · exact Or.inl (ih.1 hzero)
    · exact Or.inr (Or.inr (ih.2 hsafe))
  case case9 =>
    rename_i expression value one queries hconst hone ih ihConstants
    rintro (hzero | hsafe)
    · exact Or.inl (ih.1 hzero)
    · exact Or.inr (Or.inr (ih.2 hsafe))
  case case10 =>
    rename_i expression value queries hconst ih
    rintro (hzero | hsafe)
    · exact Or.inr (exprPartialMaskInvariant_of_publicValue known retained _ 0 (ih.1 hzero))
    · exact Or.inr (ih.2 hsafe)
  case case12 =>
    rename_i left right queries hleft hright hrightConst ihLeft ihRight
    constructor
    · rintro (hleft | hright) hleftZero hrightZero
      · exact False.elim (hleftZero (ihLeft.1 hleft))
      · exact False.elim (hrightZero (ihRight.1 hright))
    · rintro ((hleft | hright) | ⟨hleft, hright⟩)
      · exact Or.inl (ihLeft.1 hleft)
      · exact Or.inr (Or.inl (ihRight.1 hright))
      · exact Or.inr (Or.inr ⟨ihLeft.2 hleft, ihRight.2 hright⟩)

end Zcash.Snark.ZeroKnowledge
