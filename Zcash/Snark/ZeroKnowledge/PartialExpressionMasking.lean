import Zcash.Snark.ZeroKnowledge.ExpressionMasking

/-!
# Mask checks from partial public fixed-column information

Unknown fixed values remain public but cannot be used to certify a zero factor.
Every value and mask check computed with the partial information refines the
existing full-information checker for every compatible fixed assignment. This lets
selector-only certificates ignore unrelated table and region-fixed constants.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- Evaluate using the known fixed values; `none` supplies no information about a query. -/
def exprPartialPublicValue (known : ℕ → Option F) : Expr F → Option F
  | .constant c => some c
  | .fixed i => known i
  | .instance _ | .advice _ => none
  | .negated e => (exprPartialPublicValue known e).map Neg.neg
  | .sum left right =>
      (exprPartialPublicValue known left).bind fun x => (exprPartialPublicValue known right).map (x + ·)
  | .product left right =>
      let x := exprPartialPublicValue known left
      let y := exprPartialPublicValue known right
      if x = some 0 then some 0 else if y = some 0 then some 0
      else x.bind fun a => y.map (a * ·)
  | .scaled e c =>
      if c = 0 then some 0 else (exprPartialPublicValue known e).map (· * c)

/-- A partial public value is also computed by the full checker for every compatible assignment. -/
theorem exprPartialPublicValue_refines (known : ℕ → Option F) (fixed : ℕ → F)
    (hagrees : ∀ query value, known query = some value → fixed query = value)
    (expr : Expr F) (value : F) (hvalue : exprPartialPublicValue known expr = some value) :
    exprPublicValue fixed expr = some value := by
  induction expr generalizing value with
  | constant c => exact hvalue
  | fixed i => exact congrArg some (hagrees i value hvalue)
  | «instance» i => simp [exprPartialPublicValue] at hvalue
  | advice i => simp [exprPartialPublicValue] at hvalue
  | negated e ih =>
      cases he : exprPartialPublicValue known e with
      | none => simp [exprPartialPublicValue, he] at hvalue
      | some v =>
          simpa only [exprPartialPublicValue, he, Option.map_some, exprPublicValue, ih v he] using hvalue
  | sum left right ihLeft ihRight =>
      cases hl : exprPartialPublicValue known left with
      | none => simp [exprPartialPublicValue, hl] at hvalue
      | some x =>
          cases hr : exprPartialPublicValue known right with
          | none => simp [exprPartialPublicValue, hl, hr] at hvalue
          | some y =>
              simpa only [exprPartialPublicValue, hl, hr, Option.bind_some, Option.map_some,
                exprPublicValue, ihLeft x hl, ihRight y hr] using hvalue
  | product left right ihLeft ihRight =>
      by_cases hl0 : exprPartialPublicValue known left = some 0
      · simpa only [exprPartialPublicValue, if_pos hl0, exprPublicValue,
          ihLeft 0 hl0, if_pos rfl] using hvalue
      · by_cases hr0 : exprPartialPublicValue known right = some 0
        · have hv : (0 : F) = value := by
            simpa only [exprPartialPublicValue, if_neg hl0, if_pos hr0, Option.some.injEq] using hvalue
          rw [← hv]
          simp [exprPublicValue, ihRight 0 hr0]
        · simp only [exprPartialPublicValue] at hvalue
          rw [if_neg hl0, if_neg hr0] at hvalue
          cases hl : exprPartialPublicValue known left with
          | none => simp [hl] at hvalue
          | some x =>
              cases hr : exprPartialPublicValue known right with
              | none => simp [hl, hr] at hvalue
              | some y =>
                  have hxy : x * y = value := by
                    simpa only [hl, hr, Option.bind_some, Option.map_some, Option.some.injEq] using hvalue
                  rw [← hxy]
                  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
                    simp [exprPublicValue, ihLeft x hl, ihRight y hr, hx, hy]
  | scaled e c ih =>
      by_cases hc : c = 0
      · simpa only [exprPartialPublicValue, exprPublicValue, if_pos hc] using hvalue
      · cases he : exprPartialPublicValue known e with
        | none => simp [exprPartialPublicValue, hc, he] at hvalue
        | some v =>
            simpa only [exprPartialPublicValue, if_neg hc, he, Option.map_some,
              exprPublicValue, ih v he] using hvalue

/-- Check mask invariance using only the supplied subset of public fixed values. -/
def exprPartialMaskInvariant (known : ℕ → Option F) (retained : ℕ → Bool) : Expr F → Bool
  | .constant _ | .fixed _ | .instance _ => true
  | .advice i => retained i
  | .negated e => exprPartialMaskInvariant known retained e
  | .sum left right => exprPartialMaskInvariant known retained left && exprPartialMaskInvariant known retained right
  | .product left right =>
      if exprPartialPublicValue known left = some 0 then true
      else if exprPartialPublicValue known right = some 0 then true
      else exprPartialMaskInvariant known retained left && exprPartialMaskInvariant known retained right
  | .scaled e c => if c = 0 then true else exprPartialMaskInvariant known retained e

/-- Passing the partial checker implies the existing full public mask check. -/
theorem exprPartialMaskInvariant_refines (known : ℕ → Option F) (fixed : ℕ → F)
    (hagrees : ∀ query value, known query = some value → fixed query = value)
    (retained : ℕ → Bool) (expr : Expr F)
    (hcheck : exprPartialMaskInvariant known retained expr = true) :
    exprMaskInvariant fixed retained expr = true := by
  induction expr with
  | constant c | fixed i | «instance» i => rfl
  | advice i => exact hcheck
  | negated e ih => exact ih hcheck
  | sum left right ihLeft ihRight =>
      have h : exprPartialMaskInvariant known retained left = true ∧
          exprPartialMaskInvariant known retained right = true := by
        simpa only [exprPartialMaskInvariant, Bool.and_eq_true] using hcheck
      simp only [exprMaskInvariant, ihLeft h.1, ihRight h.2, Bool.and_self]
  | product left right ihLeft ihRight =>
      by_cases hl : exprPartialPublicValue known left = some 0
      · simp [exprMaskInvariant, exprPartialPublicValue_refines known fixed hagrees left 0 hl]
      · by_cases hr : exprPartialPublicValue known right = some 0
        · simp [exprMaskInvariant, exprPartialPublicValue_refines known fixed hagrees right 0 hr]
        · have h : exprPartialMaskInvariant known retained left = true ∧
              exprPartialMaskInvariant known retained right = true := by
            simpa only [exprPartialMaskInvariant, if_neg hl, if_neg hr, Bool.and_eq_true] using hcheck
          simp [exprMaskInvariant, ihLeft h.1, ihRight h.2]
  | scaled e c ih =>
      by_cases hc : c = 0
      · simp only [exprMaskInvariant, if_pos hc]
      · have h : exprPartialMaskInvariant known retained e = true := by
          simpa only [exprPartialMaskInvariant, if_neg hc] using hcheck
        simp only [exprMaskInvariant, if_neg hc, ih h]

end Zcash.Snark.ZeroKnowledge
