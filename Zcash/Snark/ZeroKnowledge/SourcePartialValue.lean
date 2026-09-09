import Zcash.Snark.ZeroKnowledge.SourcePartialMasking

/-!
# Sound evaluation of partially known source expressions
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Every value recovered by partial multiplication agrees with full multiplication. -/
theorem partialProductValue_sound {F : Type} [Field F] [DecidableEq F]
    (left right : Option F) (a b value : F)
    (hleft : ∀ x, left = some x → x = a) (hright : ∀ y, right = some y → y = b)
    (hvalue : partialProductValue left right = some value) : value = a * b := by
  unfold partialProductValue at hvalue
  split at hvalue
  next hz =>
    have ha := hleft 0 hz
    cases hvalue
    rw [← ha, zero_mul]
  next hnonzero =>
    split at hvalue
    next hz =>
      have hb := hright 0 hz
      cases hvalue
      rw [← hb, mul_zero]
    next =>
      cases left with
      | none => cases hvalue
      | some x =>
        cases right with
        | none => cases hvalue
        | some y =>
          have ha := hleft x rfl
          have hb := hright y rfl
          cases hvalue
          rw [ha, hb]

/-- A known partial source value is valid under every compatible complete valuation. -/
theorem sourcePartialValue_sound {F : Type} [Field F] [DecidableEq F]
    (known : Query → Option F) (valuation : Query → F)
    (hagrees : ∀ query value, known query = some value → value = valuation query)
    (expression : Expression F Query) (value : F)
    (hvalue : sourcePartialValue known expression = some value) :
    value = expression.eval valuation := by
  induction expression generalizing value with
  | const scalar => exact (Option.some.inj hvalue).symm
  | var query => exact hagrees query value hvalue
  | add left right ihleft ihright =>
    simp only [sourcePartialValue] at hvalue
    cases hl : sourcePartialValue known left with
    | none => simp [hl] at hvalue
    | some a =>
      cases hr : sourcePartialValue known right with
      | none => simp [hl, hr] at hvalue
      | some b =>
        simp only [hl, hr, Option.bind_some, Option.map_some, Option.some.injEq] at hvalue
        rw [← hvalue, ihleft a hl, ihright b hr]
        rfl
  | mul left right ihleft ihright =>
    exact partialProductValue_sound _ _ _ _ value
      (fun a ha => ihleft a ha) (fun b hb => ihright b hb) hvalue

end Zcash.Snark.ZeroKnowledge
