import Zcash.Snark.ZeroKnowledge.RandomTapeSource

/-!
# Wide reduction of an arbitrary finite raw tape

Each independent uniform 512-bit word is reduced modulo the Pasta scalar-field
order. The resulting tape is exactly the existing wide-field sampling program,
for any deterministic continuation and any draw count.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- One full 512-bit input word for each field draw. -/
abbrev RawFieldTape (count : ℕ) := Fin count → Fin challengeDigestCard

/-- Apply the specified modular reduction to every word of a finite tape. -/
def reduceFieldTape {count : ℕ} (tape : RawFieldTape count) : Fin count → Fp :=
  fun i => ((tape i).val : Fp)

/-- Independent uniform raw words have exactly the existing joint wide-reduced field law. -/
theorem uniformRawFieldTape_reduce (count : ℕ) :
    (PMF.uniformOfFintype (RawFieldTape count)).map reduceFieldTape = independentTapeLaw fieldSample count := by
  rw [← independentTapeLaw_uniform (A := Fin challengeDigestCard)]
  exact (independentTapeLaw_map (PMF.uniformOfFintype (Fin challengeDigestCard))
    (fun word => (word.val : Fp)) count).symm

/-- Running a deterministic continuation on the reduced raw tape realizes its exact sampling program. -/
theorem rawFieldTape_sample_law {Output : Type*} (count : ℕ) (finish : (Fin count → Fp) → Output) :
    (PMF.uniformOfFintype (RawFieldTape count)).map (finish ∘ reduceFieldTape) =
      (sampleFieldsWith count finish).runFreshPMF fieldSample := by
  rw [sampleFieldsWith_eq_independentTape, ← uniformRawFieldTape_reduce count, PMF.map_comp]

/-- Splitting one raw tape gives independent raw responses and wide-reduced private fields. -/
theorem splitRawFieldTape_sample_law {Output : Type*} (responses fields : ℕ)
    (finish : RawFieldTape responses → (Fin fields → Fp) → Output) :
    (PMF.uniformOfFintype (RawFieldTape (responses + fields))).map (fun tape =>
      let parts := splitTapeEquiv responses fields (Fin challengeDigestCard) tape
      finish parts.1 (reduceFieldTape parts.2)) =
      (PMF.uniformOfFintype (RawFieldTape responses)).bind (fun digests =>
        (sampleFieldsWith fields (finish digests)).runFreshPMF fieldSample) := by
  have hsplit := Zcash.map_uniformOfFintype_equiv
    (splitTapeEquiv responses fields (Fin challengeDigestCard))
  have h := congrArg (PMF.map (fun parts : RawFieldTape responses × RawFieldTape fields =>
    finish parts.1 (reduceFieldTape parts.2))) hsplit
  rw [PMF.map_comp, ← Zcash.independentProductPMF_uniform] at h
  apply h.trans
  simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (RawFieldTape responses)))
  funext digests
  exact rawFieldTape_sample_law _ _

/-- The whole reduced raw tape contributes at most one wide-reduction bias per field draw. -/
theorem rawFieldTape_error_bound {Output : Type*} (count : ℕ) (finish : (Fin count → Fp) → Output) :
    PMFEventBiasLE ((PMF.uniformOfFintype (RawFieldTape count)).map (finish ∘ reduceFieldTape))
        ((PMF.uniformOfFintype (Fin count → Fp)).map finish) (count * challenge255Bias) ∧
      PMFEventBiasLE ((PMF.uniformOfFintype (Fin count → Fp)).map finish)
        ((PMF.uniformOfFintype (RawFieldTape count)).map (finish ∘ reduceFieldTape))
        (count * challenge255Bias) := by
  rw [rawFieldTape_sample_law]
  exact sampleFieldsWith_error_bound count finish

end Zcash.Snark.ZeroKnowledge
