import Zcash.Snark.ZeroKnowledge.SparseIpa
import Zcash.Snark.ZeroKnowledge.LinearMask
import Zcash.Snark.ZeroKnowledge.Sampling

/-!
# Masking bounds under the implemented wide-reduction law

These results compose the derived mask algebra with the actual field-sampling law from
the pinned description. Challenges are fixed public inputs here. The two inequalities
bound event probabilities in both directions; they do not assert exact uniformity of
the implemented samples or zero-knowledge of the entire prover.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- The sparse-mask scalar using `k` independent wide-reduced field samples. -/
noncomputable def actualSparseIpaScalar {k : ℕ} (q xi v : Fp) (rounds : Fin k → Fp)
    (coefficients : Fin (2 ^ k) → Fp) : PMF Fp :=
  (sampleFieldsWith k (maskedIpaScalar q xi v rounds coefficients)).runFreshPMF fieldSample

/-- Common #225's scalar simulator is within `k` sampling-bias terms of the implemented law. -/
theorem actualSparseIpaScalar_error_bound {k : ℕ} (q xi v : Fp) (rounds : Fin k → Fp)
    (coefficients : Fin (2 ^ k) → Fp) (hxi : xi ≠ 0)
    (hv : coefficientEvaluation k q coefficients = v) :
    PMFEventBiasLE (actualSparseIpaScalar q xi v rounds coefficients)
        (idealSparseIpaScalar q rounds) (k * challenge255Bias) ∧
      PMFEventBiasLE (idealSparseIpaScalar q rounds)
        (actualSparseIpaScalar q xi v rounds coefficients) (k * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound k (maskedIpaScalar q xi v rounds coefficients)
  rw [maskedIpaScalar_simulates q xi v rounds coefficients hxi hv] at h
  exact h

/-- The disclosed and masked evaluations using the two actual coefficient draws. -/
noncomputable def actualLinearMaskView (x q : Fp) (offset : Fp → Fp) : PMF (Fp × Fp) :=
  (sampleFieldsWith 2 (linearMaskView x q offset ∘ finTwoArrowEquiv Fp)).runFreshPMF fieldSample

/-- Common #267's joint pair is within two sampling-bias terms of a uniform pair. -/
theorem actualLinearMaskView_error_bound (x q : Fp) (offset : Fp → Fp) (hqx : q ≠ x) :
    PMFEventBiasLE (actualLinearMaskView x q offset) (PMF.uniformOfFintype (Fp × Fp))
        (2 * challenge255Bias) ∧
      PMFEventBiasLE (PMF.uniformOfFintype (Fp × Fp)) (actualLinearMaskView x q offset)
        (2 * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound 2
    (linearMaskView x q offset ∘ finTwoArrowEquiv Fp)
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    linearMaskView_uniform x q offset hqx] at h
  exact h

end Zcash.Snark.ZeroKnowledge
