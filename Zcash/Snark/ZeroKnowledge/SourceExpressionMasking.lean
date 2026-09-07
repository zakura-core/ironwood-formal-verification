import Clean.Halo2.Keygen.CompressSelectors

/-!
# Structural masking certificates for source expressions

These checks use only expression structure and query classifications. Constants
are always public, but are never inspected to establish a zero. A zero query can
annihilate an arbitrary product. The certificates can therefore be reduced without
evaluating the Action circuit's field constants or its private witness programs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Recognize expressions forced to zero by the designated zero queries. -/
def sourceExpressionZero {F : Type} (zero : Query → Bool) : Expression F Query → Bool
  | .const _ => false
  | .var query => zero query
  | .add left right => sourceExpressionZero zero left && sourceExpressionZero zero right
  | .mul left right => sourceExpressionZero zero left || sourceExpressionZero zero right

/-- Certify that unretained advice occurs only in products with a known zero factor. -/
def sourceExpressionMaskSafe {F : Type} (zero safe : Query → Bool) : Expression F Query → Bool
  | .const _ => true
  | .var query => safe query
  | .add left right => sourceExpressionMaskSafe zero safe left && sourceExpressionMaskSafe zero safe right
  | .mul left right => sourceExpressionZero zero left || sourceExpressionZero zero right ||
      (sourceExpressionMaskSafe zero safe left && sourceExpressionMaskSafe zero safe right)

/-- A structurally zero expression is mask-safe when each designated zero query is safe. -/
theorem sourceExpressionMaskSafe_of_zero {F : Type} (zero safe : Query → Bool)
    (hzero : ∀ query, zero query = true → safe query = true)
    (expression : Expression F Query) (hexpression : sourceExpressionZero zero expression = true) :
    sourceExpressionMaskSafe zero safe expression = true := by
  induction expression with
  | const => simp [sourceExpressionZero] at hexpression
  | var query => exact hzero query hexpression
  | add left right ihLeft ihRight =>
      simp only [sourceExpressionZero, Bool.and_eq_true] at hexpression
      simp only [sourceExpressionMaskSafe, ihLeft hexpression.1, ihRight hexpression.2, Bool.and_self]
  | mul left right =>
      simp only [sourceExpressionZero] at hexpression
      simp only [sourceExpressionMaskSafe, hexpression, Bool.true_or]

/-- A selector replacement is structurally zero whenever its packed query is zero. -/
theorem selReplacement_sourceExpressionZero {F : Type} [Field F]
    (zero : Query → Bool) (compressed : SelCompress)
    (hzero : zero (.fixed ⟨compressed.packedCol⟩ 0) = true) :
    sourceExpressionZero zero (selReplacement (F := F) compressed) = true := by
  unfold selReplacement
  have hfold (factors : List (Expression F Query)) (initial : Expression F Query)
      (hinitial : sourceExpressionZero zero initial = true) :
      sourceExpressionZero zero (factors.foldl (· * ·) initial) = true := by
    induction factors generalizing initial with
    | nil => exact hinitial
    | cons factor rest ih =>
        rw [List.foldl_cons]
        exact ih _ (by simp [sourceExpressionZero, hinitial])
  exact hfold _ (.var (.fixed ⟨compressed.packedCol⟩ 0)) hzero

/-- A selector replacement is public whenever its packed fixed query is public. -/
theorem selReplacement_sourceExpressionMaskSafe {F : Type} [Field F]
    (zero safe : Query → Bool) (compressed : SelCompress)
    (hsafe : safe (.fixed ⟨compressed.packedCol⟩ 0) = true) :
    sourceExpressionMaskSafe zero safe (selReplacement (F := F) compressed) = true := by
  have hfold (factors : List (Expression F Query)) (initial : Expression F Query)
      (hinitial : sourceExpressionMaskSafe zero safe initial = true)
      (hfactors : ∀ factor ∈ factors, sourceExpressionMaskSafe zero safe factor = true) :
      sourceExpressionMaskSafe zero safe (factors.foldl (· * ·) initial) = true := by
    induction factors generalizing initial with
    | nil => exact hinitial
    | cons factor rest ih =>
        rw [List.foldl_cons]
        exact ih _ (by simp [sourceExpressionMaskSafe, hinitial, hfactors factor (by simp)])
          (fun next hnext => hfactors next (by simp [hnext]))
  unfold selReplacement
  apply hfold _ (.var (.fixed ⟨compressed.packedCol⟩ 0)) hsafe
  intro factor hfactor
  obtain ⟨index, _, hfactor⟩ := List.mem_filterMap.mp hfactor
  dsimp only at hfactor
  split at hfactor
  · simp at hfactor
  · cases Option.some.inj hfactor
    simp [sourceExpressionMaskSafe, hsafe]

/-- Structural zero and safety certificates survive selector substitution under leafwise certificates. -/
theorem substSelectorMap_sourceMaskCertificates {F : Type} [Field F]
    (map : ℕ → Option SelCompress) (sourceZero sourceSafe targetZero targetSafe : Query → Bool)
    (hzero : ∀ query, sourceZero query = true →
      sourceExpressionZero targetZero (substSelectorMap map (.var query : Expression F Query)) = true)
    (hsafe : ∀ query, sourceSafe query = true →
      sourceExpressionMaskSafe targetZero targetSafe
        (substSelectorMap map (.var query : Expression F Query)) = true)
    (expression : Expression F Query) :
    (sourceExpressionZero sourceZero expression = true →
      sourceExpressionZero targetZero (substSelectorMap map expression) = true) ∧
    (sourceExpressionMaskSafe sourceZero sourceSafe expression = true →
      sourceExpressionMaskSafe targetZero targetSafe (substSelectorMap map expression) = true) := by
  induction expression with
  | const value => simp [sourceExpressionZero, sourceExpressionMaskSafe, substSelectorMap]
  | var query => exact ⟨hzero query, hsafe query⟩
  | add left right ihLeft ihRight =>
      simp only [sourceExpressionZero, sourceExpressionMaskSafe, substSelectorMap, Bool.and_eq_true]
      exact ⟨fun h => ⟨ihLeft.1 h.1, ihRight.1 h.2⟩,
        fun h => ⟨ihLeft.2 h.1, ihRight.2 h.2⟩⟩
  | mul left right ihLeft ihRight =>
      simp only [sourceExpressionZero, sourceExpressionMaskSafe, substSelectorMap,
        Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · exact Or.imp ihLeft.1 ihRight.1
      · rintro ((hleft | hright) | ⟨hleft, hright⟩)
        · exact Or.inl (Or.inl (ihLeft.1 hleft))
        · exact Or.inl (Or.inr (ihRight.1 hright))
        · exact Or.inr ⟨ihLeft.2 hleft, ihRight.2 hright⟩

end Zcash.Snark.ZeroKnowledge
