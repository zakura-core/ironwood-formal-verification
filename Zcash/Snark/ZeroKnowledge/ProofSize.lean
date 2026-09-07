import Zcash.Snark.ZeroKnowledge.PlonkAttempt

/-!
# Size of the actual reference proof

The count follows the existing transcript and proof constructors, including the
two optional permutation evaluations that are present for each Action. Challenges
and common inputs contribute no proof items. At eleven IPA rounds the result is
85 + 71m items, which gives the specified 2720 + 2272m bytes for 32-byte encodings.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Flattening message stages adds their proof-item counts. -/
@[simp] theorem protocolMessageCount_flatten {F G : Type*}
    (stages : List (List (TranscriptElt F G))) :
    protocolMessageCount stages.flatten = (stages.map protocolMessageCount).sum := by
  induction stages with
  | nil => rfl
  | cons stage stages ih => simp [ih]

private theorem messages_points {F G : Type*} (points : List G) :
    protocolMessageCount (points.map (TranscriptElt.point (F := F))) = points.length := by
  induction points with
  | nil => rfl
  | cons point points ih => simp [protocolMessageCount, ih, Nat.add_comm]

private theorem messages_scalars {F G : Type*} (scalars : List F) :
    protocolMessageCount (scalars.map (TranscriptElt.scalar (G := G))) = scalars.length := by
  induction scalars with
  | nil => rfl
  | cons scalar scalars ih => simp [protocolMessageCount, ih, Nat.add_comm]

private theorem messages_absorbPoints {F G : Type*} {n : ℕ} (points : Fin n → G) :
    protocolMessageCount (absorbPoints (F := F) points) = n := by
  simpa only [List.map_ofFn, List.length_ofFn, absorbPoints] using
    messages_points (F := F) (List.ofFn points)

private theorem messages_absorbScalars {F G : Type*} {n : ℕ} (scalars : Fin n → F) :
    protocolMessageCount (absorbScalars (G := G) scalars) = n := by
  simpa only [List.map_ofFn, List.length_ofFn, absorbScalars] using
    messages_scalars (G := G) (List.ofFn scalars)

private theorem messages_absorbPoints2 {F G : Type*} {a b : ℕ} (points : Fin a → Fin b → G) :
    protocolMessageCount (absorbPoints2 (F := F) points) = a * b := by
  simp [absorbPoints2, messages_absorbPoints, List.map_ofFn, Function.comp_def]

private theorem messages_absorbScalars2 {F G : Type*} {a b : ℕ} (scalars : Fin a → Fin b → F) :
    protocolMessageCount (absorbScalars2 (G := G) scalars) = a * b := by
  simp [absorbScalars2, messages_absorbScalars, List.map_ofFn, Function.comp_def]

private theorem messages_absorbLookupPermuted {F G : Type*} {a b : ℕ}
    (input table : Fin a → Fin b → G) :
    protocolMessageCount (absorbLookupPermuted (F := F) input table) = 2 * a * b := by
  simp [absorbLookupPermuted, List.map_ofFn, Function.comp_def, protocolMessageCount]
  ring

private theorem messages_absorbLookup {F G : Type*} (evals : LookupEval F) :
    protocolMessageCount (absorbLookup (G := G) evals) = 5 := rfl

/-- Count all actual reference-proof items, including the prescribed optional evaluations. -/
theorem plonkProofString_messageCount {actions k : ℕ} {F G : Type*}
    (instances : Fin actions → F) (fixed : Fin 29 → F) (sigma : Fin 15 → F)
    (column : PrivateColumnId actions → Fin 4 → F)
    (points : Fin (22 * actions + 10) → G) (rEval : F) (groupValues : Fin 5 → F)
    (tail : IpaTranscript k F G) :
    protocolMessageCount (plonkAttemptTrace
      (plonkProofString instances fixed sigma column points rEval groupValues tail)) =
        71 * actions + 63 + 2 * k := by
  let proof := plonkProofString instances fixed sigma column points rEval groupValues tail
  have hper (a : Fin actions) :
      ∑ s : Fin 3, protocolMessageCount (absorbPermSet (G := G)
        (proof.permutationSetEvals a s)) = 8 := by
    simp [proof, plonkProofString, Fin.sum_univ_succ, absorbPermSet, protocolMessageCount]
  change protocolMessageCount (plonkAttemptTrace proof) = _
  simp only [plonkAttemptTrace, preIpaTranscript, protocolMessageCount_append,
    messages_absorbPoints2, messages_absorbPoints, messages_absorbScalars2,
    messages_absorbScalars, messages_absorbLookupPermuted, protocolMessageCount_flatten,
    List.map_ofFn, Function.comp_def, messages_absorbLookup, protocolMessageCount]
  simp only [plonkProofShape, FixtureMax.shape, List.sum_ofFn, hper, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The joint-view adapter preserves the exact proof-item count. -/
theorem plonkProofFromJointView_messageCount {actions k : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    protocolMessageCount (plonkAttemptTrace (plonkProofFromJointView pub x x1 view)) =
      71 * actions + 63 + 2 * k :=
  plonkProofString_messageCount _ _ _ _ _ _ _ _

end Zcash.Snark.ZeroKnowledge
