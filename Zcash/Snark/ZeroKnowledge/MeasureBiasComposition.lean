import Zcash.Snark.ZeroKnowledge.MeasureEventBias

/-!
# Composition of measured-view simulation errors

The error terms compose as probability bounds. An observed infinite stream is
kept as a probability measure; only finite-output reductions use PMFs.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- A larger error also bounds every measurable event difference. -/
theorem MeasureEventBiasLE.mono {A : Type*} [MeasurableSpace A]
    {actual ideal : Measure A} {error bound : ℝ≥0∞}
    (h : MeasureEventBiasLE actual ideal error) (hle : error ≤ bound) :
    MeasureEventBiasLE actual ideal bound :=
  fun event he => (h event he).trans (add_le_add le_rfl hle)

/-- Measured-view comparisons compose with the sum of their two error terms. -/
theorem MeasureEventBiasLE.trans {A : Type*} [MeasurableSpace A]
    {actual middle ideal : Measure A} {first second : ℝ≥0∞}
    (hfirst : MeasureEventBiasLE actual middle first)
    (hsecond : MeasureEventBiasLE middle ideal second) :
    MeasureEventBiasLE actual ideal (first + second) := by
  intro event he
  exact (hfirst event he).trans (by
    simpa only [add_assoc, add_comm second first] using add_le_add (hsecond event he) (le_refl first))

/-- A measurable test after a discrete-to-stream observation is exactly the composed finite test. -/
theorem pmfObservedMeasure_map {A B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (source : PMF A) (observe : A → B) (test : B → C) (hmeasurable : Measurable test) :
    ((source.map observe).toMeasure).map test =
      (source.map (fun value => test (observe value))).toMeasure := by
  rw [PMF.toMeasure_map _ _ hmeasurable, PMF.map_comp]
  rfl

end Zcash.Snark.ZeroKnowledge
