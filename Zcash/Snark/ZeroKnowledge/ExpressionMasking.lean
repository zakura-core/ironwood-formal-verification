import Zcash.Snark.Verifier.Expressions

/-!
# Public expression checks for advice-mask invariance

The checker tracks advice queries whose values are retained and recognizes products
annihilated by public zero factors. Its inputs contain no private advice. A successful
check proves equality for any two advice valuations agreeing at the retained queries;
failure of the check makes no claim that the expression actually depends on a mask.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- Evaluate constants and fixed queries, also recognizing products with a fixed zero factor. -/
def exprPublicValue (fixed : ℕ → F) : Expr F → Option F
  | .constant c => some c
  | .fixed i => some (fixed i)
  | .instance _ => none
  | .advice _ => none
  | .negated e => (exprPublicValue fixed e).map Neg.neg
  | .sum left right =>
      (exprPublicValue fixed left).bind fun x => (exprPublicValue fixed right).map (x + ·)
  | .product left right =>
      let x := exprPublicValue fixed left
      let y := exprPublicValue fixed right
      if x = some 0 then some 0 else if y = some 0 then some 0
      else x.bind fun a => y.map (a * ·)
  | .scaled e c =>
      if c = 0 then some 0 else (exprPublicValue fixed e).map (· * c)

/-- A value computed from fixed queries is valid for every advice and instance assignment. -/
theorem exprPublicValue_sound (fixed inst advice : ℕ → F) (expr : Expr F) (value : F)
    (hvalue : exprPublicValue fixed expr = some value) :
    expr.eval fixed advice inst = value := by
  induction expr generalizing value with
  | constant c => exact Option.some.inj hvalue
  | fixed i => exact Option.some.inj hvalue
  | «instance» i => simp [exprPublicValue] at hvalue
  | advice i => simp [exprPublicValue] at hvalue
  | negated e ih =>
      cases he : exprPublicValue fixed e with
      | none => simp [exprPublicValue, he] at hvalue
      | some v =>
          have hv := ih v he
          simpa only [exprPublicValue, he, Option.map_some, Option.some.injEq, Expr.eval, hv] using hvalue
  | sum left right ihLeft ihRight =>
      cases hl : exprPublicValue fixed left with
      | none => simp [exprPublicValue, hl] at hvalue
      | some x =>
          cases hr : exprPublicValue fixed right with
          | none => simp [exprPublicValue, hl, hr] at hvalue
          | some y =>
              have hx := ihLeft x hl
              have hy := ihRight y hr
              simpa only [exprPublicValue, hl, hr, Option.bind_some, Option.map_some,
                Option.some.injEq, Expr.eval, hx, hy] using hvalue
  | product left right ihLeft ihRight =>
      by_cases hl0 : exprPublicValue fixed left = some 0
      · have hl := ihLeft 0 hl0
        simpa only [exprPublicValue, if_pos hl0, Option.some.injEq, Expr.eval, hl, zero_mul] using hvalue
      · by_cases hr0 : exprPublicValue fixed right = some 0
        · have hr := ihRight 0 hr0
          simpa only [exprPublicValue, if_neg hl0, if_pos hr0, Option.some.injEq, Expr.eval, hr, mul_zero] using hvalue
        · simp only [exprPublicValue] at hvalue
          rw [if_neg hl0, if_neg hr0] at hvalue
          cases hl : exprPublicValue fixed left with
          | none => simp [hl] at hvalue
          | some x =>
              cases hr : exprPublicValue fixed right with
              | none => simp [hl, hr] at hvalue
              | some y =>
                  have hx := ihLeft x hl
                  have hy := ihRight y hr
                  simpa only [hl, hr,
                    Option.bind_some, Option.map_some, Option.some.injEq, Expr.eval, hx, hy] using hvalue
  | scaled e c ih =>
      by_cases hc : c = 0
      · have hv : (0 : F) = value := by
          simpa only [exprPublicValue, if_pos hc, Option.some.injEq] using hvalue
        simpa only [Expr.eval, hc, mul_zero] using hv
      · cases he : exprPublicValue fixed e with
        | none => simp [exprPublicValue, hc, he] at hvalue
        | some v =>
            have hv := ih v he
            simpa only [exprPublicValue, if_neg hc, he, Option.map_some, Option.some.injEq, Expr.eval, hv] using hvalue

/-- Check that all effective advice dependencies are retained, using public zero selectors. -/
def exprMaskInvariant (fixed : ℕ → F) (retained : ℕ → Bool) : Expr F → Bool
  | .constant _ | .fixed _ | .instance _ => true
  | .advice i => retained i
  | .negated e => exprMaskInvariant fixed retained e
  | .sum left right => exprMaskInvariant fixed retained left && exprMaskInvariant fixed retained right
  | .product left right =>
      if exprPublicValue fixed left = some 0 then true
      else if exprPublicValue fixed right = some 0 then true
      else exprMaskInvariant fixed retained left && exprMaskInvariant fixed retained right
  | .scaled e c => if c = 0 then true else exprMaskInvariant fixed retained e

/-- If every advice query is retained, every expression passes without inspecting selector values. -/
theorem exprMaskInvariant_of_retained_all (fixed : ℕ → F) (retained : ℕ → Bool)
    (hall : ∀ query, retained query = true) (expr : Expr F) :
    exprMaskInvariant fixed retained expr = true := by
  induction expr <;> simp_all [exprMaskInvariant]

/-- Passing the public check makes an expression invariant under arbitrary changes to other advice. -/
theorem exprMaskInvariant_sound (fixed inst : ℕ → F) (retained : ℕ → Bool)
    (left right : ℕ → F) (hagrees : ∀ i, retained i = true → left i = right i)
    (expr : Expr F) (hcheck : exprMaskInvariant fixed retained expr = true) :
    expr.eval fixed left inst = expr.eval fixed right inst := by
  induction expr with
  | constant c => rfl
  | fixed i => rfl
  | «instance» i => rfl
  | advice i => exact hagrees i hcheck
  | negated e ih => exact congrArg Neg.neg (ih hcheck)
  | sum a b ihA ihB =>
      have h : exprMaskInvariant fixed retained a = true ∧ exprMaskInvariant fixed retained b = true := by
        simpa only [exprMaskInvariant, Bool.and_eq_true] using hcheck
      exact congrArg₂ (· + ·) (ihA h.1) (ihB h.2)
  | product a b ihA ihB =>
      by_cases ha : exprPublicValue fixed a = some 0
      · simp only [Expr.eval, exprPublicValue_sound fixed inst left a 0 ha,
          exprPublicValue_sound fixed inst right a 0 ha, zero_mul]
      · by_cases hb : exprPublicValue fixed b = some 0
        · simp only [Expr.eval, exprPublicValue_sound fixed inst left b 0 hb,
            exprPublicValue_sound fixed inst right b 0 hb, mul_zero]
        · have h : exprMaskInvariant fixed retained a = true ∧ exprMaskInvariant fixed retained b = true := by
            simpa only [exprMaskInvariant, if_neg ha, if_neg hb, Bool.and_eq_true] using hcheck
          exact congrArg₂ (· * ·) (ihA h.1) (ihB h.2)
  | scaled e c ih =>
      by_cases hc : c = 0
      · simp only [Expr.eval, hc, mul_zero]
      · exact congrArg (· * c) (ih (by simpa only [exprMaskInvariant, if_neg hc] using hcheck))

end Zcash.Snark.ZeroKnowledge
