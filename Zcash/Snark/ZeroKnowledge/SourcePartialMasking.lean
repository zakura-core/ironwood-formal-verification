import Zcash.Snark.ZeroKnowledge.SourceExpressionMasking

/-!
# Source masking with evaluated public factors

An inactive selector replacement can vanish at a nonzero packed root. Evaluating
public factors recognizes this case while retaining the original source masking
certificates. Unknown values remain unknown unless a known zero annihilates them.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

variable {F : Type} [Field F] [DecidableEq F]

/-- Partial multiplication retains the absorbing known-zero cases. -/
def partialProductValue (left right : Option F) : Option F :=
  if left = some 0 then some 0 else if right = some 0 then some 0
  else left.bind fun x => right.map (x * ·)

/-- Two known partial factors produce their ordinary product, supplying the fully available
expression case. -/
@[simp]
theorem partialProductValue_some (left right : F) :
    partialProductValue (some left) (some right) = some (left * right) := by
  by_cases hleft : left = 0 <;> by_cases hright : right = 0 <;>
    simp [partialProductValue, hleft, hright]

/-- A known zero left factor fixes the product even when the other factor is unavailable, justifying
selector-masked reads. -/
@[simp]
theorem partialProductValue_zero_left (right : Option F) :
    partialProductValue (some 0) right = some 0 := by simp [partialProductValue]

/-- A known zero right factor fixes the product even when the other factor is unavailable,
justifying selector-masked reads. -/
@[simp]
theorem partialProductValue_zero_right (left : Option F) :
    partialProductValue left (some 0) = some 0 := by simp [partialProductValue]

/-- A known scalar either annihilates the product or scales the available value, exposing the
partial evaluator's scalar case. -/
theorem partialProductValue_scalar_right (left : Option F) (right : F) :
    partialProductValue left (some right) =
      if right = 0 then some 0 else left.map (· * right) := by
  cases left with
  | none => by_cases hright : right = 0 <;> simp [partialProductValue, hright]
  | some left => by_cases hright : right = 0 <;> simp [hright]

/-- Multiplication by negative one preserves availability and negates the value, connecting the
partial evaluator to expression negation. -/
theorem partialProductValue_neg_one (right : Option F) :
    partialProductValue (some (-1)) right = right.map Neg.neg := by
  cases right with
  | none => simp [partialProductValue]
  | some right => simp

/-- Evaluate source expressions using the supplied partial query valuation. -/
def sourcePartialValue (known : Query → Option F) : Expression F Query → Option F
  | .const value => some value
  | .var query => known query
  | .add left right =>
      (sourcePartialValue known left).bind fun x => (sourcePartialValue known right).map (x + ·)
  | .mul left right => partialProductValue (sourcePartialValue known left) (sourcePartialValue known right)

/-- Retain a source expression whenever all unsafe reads occur under evaluated zero factors. -/
def sourcePartialMaskSafe (known : Query → Option F) (safe : Query → Bool) : Expression F Query → Bool
  | .const _ => true
  | .var query => safe query
  | .add left right => sourcePartialMaskSafe known safe left && sourcePartialMaskSafe known safe right
  | .mul left right =>
      if sourcePartialValue known left = some 0 then true
      else if sourcePartialValue known right = some 0 then true
      else sourcePartialMaskSafe known safe left && sourcePartialMaskSafe known safe right

/-- Structural source certificates survive substitution when each zero leaf has
zero evaluated replacement value and each safe leaf has a safe replacement. -/
theorem substSelectorMap_partialMaskCertificates
    (map : ℕ → Option SelCompress) (sourceZero sourceSafe : Query → Bool)
    (known : Query → Option F) (safe : Query → Bool)
    (hzero : ∀ query, sourceZero query = true →
      sourcePartialValue known (substSelectorMap map (.var query)) = some 0)
    (hsafe : ∀ query, sourceSafe query = true →
      sourcePartialMaskSafe known safe (substSelectorMap map (.var query)) = true)
    (expression : Expression F Query) :
    (sourceExpressionZero sourceZero expression = true →
      sourcePartialValue known (substSelectorMap map expression) = some 0) ∧
    (sourceExpressionMaskSafe sourceZero sourceSafe expression = true →
      sourcePartialMaskSafe known safe (substSelectorMap map expression) = true) := by
  induction expression with
  | const value => simp [sourceExpressionZero, sourceExpressionMaskSafe, substSelectorMap, sourcePartialMaskSafe]
  | var query => exact ⟨hzero query, hsafe query⟩
  | add left right ihLeft ihRight =>
      simp only [sourceExpressionZero, sourceExpressionMaskSafe, Bool.and_eq_true]
      constructor
      · rintro ⟨hleft, hright⟩
        simp [substSelectorMap, sourcePartialValue, ihLeft.1 hleft, ihRight.1 hright]
      · rintro ⟨hleft, hright⟩
        simp [substSelectorMap, sourcePartialMaskSafe, ihLeft.2 hleft, ihRight.2 hright]
  | mul left right ihLeft ihRight =>
      simp only [sourceExpressionZero, sourceExpressionMaskSafe, Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · rintro (hleft | hright)
        · simp [substSelectorMap, sourcePartialValue, ihLeft.1 hleft]
        · simp [substSelectorMap, sourcePartialValue, ihRight.1 hright]
      · rintro ((hleft | hright) | ⟨hleft, hright⟩)
        · simp [substSelectorMap, sourcePartialMaskSafe, ihLeft.1 hleft]
        · simp [substSelectorMap, sourcePartialMaskSafe, ihRight.1 hright]
        · simp [substSelectorMap, sourcePartialMaskSafe, ihLeft.2 hleft, ihRight.2 hright]

/-- A selector replacement is safe whenever its sole packed fixed query is safe. -/
theorem selReplacement_sourcePartialMaskSafe (known : Query → Option F) (safe : Query → Bool)
    (compressed : SelCompress) (hsafe : safe (.fixed ⟨compressed.packedCol⟩ 0) = true) :
    sourcePartialMaskSafe known safe (selReplacement compressed) = true := by
  have hfold (factors : List (Expression F Query)) (initial : Expression F Query)
      (hinitial : sourcePartialMaskSafe known safe initial = true)
      (hfactors : ∀ factor ∈ factors, sourcePartialMaskSafe known safe factor = true) :
      sourcePartialMaskSafe known safe (factors.foldl (· * ·) initial) = true := by
    induction factors generalizing initial with
    | nil => exact hinitial
    | cons factor rest ih =>
        rw [List.foldl_cons]
        exact ih _ (by simp [sourcePartialMaskSafe, hinitial, hfactors factor (by simp)])
          (fun next hnext => hfactors next (by simp [hnext]))
  unfold selReplacement
  apply hfold _ (.var (.fixed ⟨compressed.packedCol⟩ 0)) hsafe
  intro factor hfactor
  obtain ⟨index, _, hfactor⟩ := List.mem_filterMap.mp hfactor
  dsimp only at hfactor
  split at hfactor
  · simp at hfactor
  · cases Option.some.inj hfactor
    simp [sourcePartialMaskSafe, hsafe]

/-- With its single fixed query known, the partial evaluator computes the entire
replacement polynomial's value. -/
theorem selReplacement_sourcePartialValue (known : Query → Option F) (valuation : Query → F)
    (compressed : SelCompress)
    (hknown : known (.fixed ⟨compressed.packedCol⟩ 0) =
      some (valuation (.fixed ⟨compressed.packedCol⟩ 0))) :
    sourcePartialValue known (selReplacement compressed) = some ((selReplacement compressed).eval valuation) := by
  have hfold (factors : List (Expression F Query)) (initial : Expression F Query)
      (hinitial : sourcePartialValue known initial = some (initial.eval valuation))
      (hfactors : ∀ factor ∈ factors, sourcePartialValue known factor = some (factor.eval valuation)) :
      sourcePartialValue known (factors.foldl (· * ·) initial) =
        some ((factors.foldl (· * ·) initial).eval valuation) := by
    induction factors generalizing initial with
    | nil => exact hinitial
    | cons factor rest ih =>
        rw [List.foldl_cons]
        apply ih
        · simp [sourcePartialValue, hinitial, hfactors factor (by simp), Expression.eval]
        · intro next hnext
          exact hfactors next (by simp [hnext])
  unfold selReplacement
  apply hfold _ (.var (.fixed ⟨compressed.packedCol⟩ 0)) hknown
  intro factor hfactor
  obtain ⟨index, _, hfactor⟩ := List.mem_filterMap.mp hfactor
  dsimp only at hfactor
  split at hfactor
  · simp at hfactor
  · cases Option.some.inj hfactor
    simp [sourcePartialValue, hknown, Expression.eval]

end Zcash.Snark.ZeroKnowledge
