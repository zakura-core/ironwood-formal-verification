import Zcash.Snark.ZeroKnowledge.CommitmentMask
import Zcash.Snark.ZeroKnowledge.LinearMask
import Zcash.Snark.ZeroKnowledge.Sampling

/-!
# The linear mask together with both blinded commitments

This projection of Common #267 retains `R`, `r(x)`, the commitment to `Q'`, and the
later masked group evaluation. Its unblinded `Q'` commitment may depend arbitrarily on
both mask coefficients. Its later additive offset may depend on the disclosed `r(x)`.
The two fresh commitment blinds remove correlations between those points and the two
evaluations, under supplied distinct evaluation points.

The statements concern this projection, including all four of its fields. They do not
claim that the remaining PLONK transcript has a witness-independent distribution or
justify the challenge schedule of a Fiat–Shamir execution.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The four disclosed fields affected by the two-coefficient mask. -/
@[ext] structure LinearMaskTranscript (F G : Type*) where
  maskCommitment : G
  firstEvaluation : F
  quotientCommitment : G
  groupEvaluation : F

/-- Put the two points and two scalars in their transcript roles. -/
def LinearMaskTranscript.ofParts (parts : (Fin 2 → G) × (F × F)) :
    LinearMaskTranscript F G where
  maskCommitment := parts.1 0
  firstEvaluation := parts.2.1
  quotientCommitment := parts.1 1
  groupEvaluation := parts.2.2

/-- The linear mask's two-generator commitment and the unblinded `Q'` commitment. -/
def linearMaskCommitmentCores (g0 g1 : G) (qPrimeCore : F × F → G)
    (coefficients : F × F) : Fin 2 → G :=
  ![coefficients.1 • g0 + coefficients.2 • g1, qPrimeCore coefficients]

/-- Compute both commitments and both evaluations from the actual coefficients and blinds. -/
def honestLinearMaskTranscript (W g0 g1 : G) (x q : F) (offset : F → F)
    (qPrimeCore : F × F → G) (coefficients : F × F) (blinds : Fin 2 → F) :
    LinearMaskTranscript F G :=
  LinearMaskTranscript.ofParts
    (blindedCommitments W (linearMaskCommitmentCores g0 g1 qPrimeCore coefficients) blinds,
      linearMaskView x q offset coefficients)

/-- Ideal independent mask coefficients and the two fresh commitment blinds. -/
noncomputable def idealLinearMaskProver [Fintype F] (W g0 g1 : G) (x q : F)
    (offset : F → F) (qPrimeCore : F × F → G) : PMF (LinearMaskTranscript F G) :=
  (PMF.uniformOfFintype (F × F)).bind fun coefficients =>
    (PMF.uniformOfFintype (Fin 2 → F)).map
      (honestLinearMaskTranscript W g0 g1 x q offset qPrimeCore coefficients)

/-- The simulator's four-field distribution has no witness or polynomial input. -/
noncomputable def idealLinearMaskSimulator [Fintype F] [Fintype G] :
    PMF (LinearMaskTranscript F G) :=
  (PMF.uniformOfFintype ((Fin 2 → G) × (F × F))).map LinearMaskTranscript.ofParts

/-- The ideal linear-mask transcript is a public map of the commitment view, allowing commitment
hiding to imply transcript hiding. -/
private theorem idealLinearMaskProver_eq_commitmentView [Fintype F]
    (W g0 g1 : G) (x q : F) (offset : F → F) (qPrimeCore : F × F → G) :
    idealLinearMaskProver W g0 g1 x q offset qPrimeCore =
      (commitmentView (F := F) W (linearMaskCommitmentCores g0 g1 qPrimeCore)
        (linearMaskView x q offset) (PMF.uniformOfFintype (F × F))).map
          LinearMaskTranscript.ofParts := by
  simp only [idealLinearMaskProver, commitmentView, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  rfl

/-- Exact joint simulation of the linear-mask projection under ideal field randomness.

This includes the first evaluation and the two commitments. The unblinded quotient point
may depend on both coefficients, so hiding is proved jointly rather than assumed from
separate scalar and group marginals. -/
theorem idealLinearMask_simulation_capstone [Fintype F] [Fintype G]
    (W g0 g1 : G) (x q : F) (offset : F → F) (qPrimeCore : F × F → G)
    (hW : Function.Bijective (fun r : F => r • W)) (hq : q ≠ x) :
    idealLinearMaskProver W g0 g1 x q offset qPrimeCore =
      idealLinearMaskSimulator (F := F) (G := G) := by
  rw [idealLinearMaskProver_eq_commitmentView, commitmentView_eq _ _ _ _ hW,
    linearMaskView_uniform x q offset hq, Zcash.independentProductPMF_uniform]
  rfl

/-- Reparameterize four samples as `(a, b)` followed by the two independent blinds.

In a complete prover these four draws are separated by other work. This is their ordered
subsequence, not a claim that the global tape consumes them consecutively. -/
def linearMaskTapeEquiv (F : Type*) : (Fin 4 → F) ≃ ((F × F) × (Fin 2 → F)) :=
  (splitTapeEquiv 2 2 F).trans
    (Equiv.prodCongr (finTwoArrowEquiv F) (Equiv.refl (Fin 2 → F)))

omit [Field F] in
/-- The selected samples are exactly the two coefficients and the two blinds in that order. -/
theorem linearMaskTapeEquiv_apply (tape : Fin 4 → F) :
    linearMaskTapeEquiv F tape = ((tape 0, tape 1), ![tape 2, tape 3]) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

/-- The four-field view computed from the selected samples. -/
def linearMaskTranscriptFromTape (W g0 g1 : G) (x q : F) (offset : F → F)
    (qPrimeCore : F × F → G) (tape : Fin 4 → F) : LinearMaskTranscript F G :=
  let coins := linearMaskTapeEquiv F tape
  honestLinearMaskTranscript W g0 g1 x q offset qPrimeCore coins.1 coins.2

/-- Uniform selected samples give the exact ideal joint law. -/
theorem uniformTapeLinearMask_eq_idealProver [Fintype F]
    (W g0 g1 : G) (x q : F) (offset : F → F) (qPrimeCore : F × F → G) :
    (PMF.uniformOfFintype (Fin 4 → F)).map
        (linearMaskTranscriptFromTape W g0 g1 x q offset qPrimeCore) =
      idealLinearMaskProver W g0 g1 x q offset qPrimeCore := by
  change (PMF.uniformOfFintype (Fin 4 → F)).map
      ((fun coins : (F × F) × (Fin 2 → F) =>
        honestLinearMaskTranscript W g0 g1 x q offset qPrimeCore coins.1 coins.2) ∘
          linearMaskTapeEquiv F) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform]
  simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp,
    Function.comp_def, idealLinearMaskProver]

/-- Run the simulator from four field coins using only multiplication by the public `W`.

The first two coins are the two disclosed scalars, and the last two sample the group points.
There is no inverse discrete-log operation in this computation. -/
def linearMaskSimulatorFromTape (W : G) (tape : Fin 4 → F) : LinearMaskTranscript F G :=
  let coins := linearMaskTapeEquiv F tape
  LinearMaskTranscript.ofParts (blindedCommitments W (fun _ => 0) coins.2, coins.1)

/-- The field-coin implementation realizes the simulator's declared joint law. -/
theorem linearMaskSimulatorFromTape_uniform [Fintype F] [Fintype G]
    (W : G) (hW : Function.Bijective (fun r : F => r • W)) :
    (PMF.uniformOfFintype (Fin 4 → F)).map (linearMaskSimulatorFromTape W) =
      idealLinearMaskSimulator (F := F) (G := G) := by
  calc
    _ = (commitmentView (F := F) W (fun _ : F × F => fun _ : Fin 2 => 0) id
        (PMF.uniformOfFintype (F × F))).map LinearMaskTranscript.ofParts := by
      change (PMF.uniformOfFintype (Fin 4 → F)).map
          ((fun coins : (F × F) × (Fin 2 → F) =>
            LinearMaskTranscript.ofParts (blindedCommitments W (fun _ => 0) coins.2, coins.1)) ∘
              linearMaskTapeEquiv F) = _
      rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
        ← Zcash.independentProductPMF_uniform]
      simp only [Zcash.independentProductPMF, commitmentView, PMF.map_bind, PMF.map_comp,
        Function.comp_def, id_eq]
    _ = _ := by
      rw [commitmentView_eq _ _ _ _ hW, PMF.map_id, Zcash.independentProductPMF_uniform]
      rfl

/-- This projection under the wide-reduced field sampler. -/
noncomputable def sampledLinearMaskProver (W g0 g1 : G) [Module Fp G]
    (x q : Fp) (offset : Fp → Fp) (qPrimeCore : Fp × Fp → G) :
    PMF (LinearMaskTranscript Fp G) :=
  (sampleFieldsWith 4 (linearMaskTranscriptFromTape W g0 g1 x q offset qPrimeCore)).runFreshPMF
    fieldSample

/-- The joint linear-mask projection is within four single-sample biases of its simulator. -/
theorem sampledLinearMask_simulation_error_bound [Module Fp G] [Fintype G]
    (W g0 g1 : G) (x q : Fp) (offset : Fp → Fp) (qPrimeCore : Fp × Fp → G)
    (hW : Function.Bijective (fun r : Fp => r • W)) (hq : q ≠ x) :
    PMFEventBiasLE (sampledLinearMaskProver W g0 g1 x q offset qPrimeCore)
        (idealLinearMaskSimulator (F := Fp) (G := G)) (4 * challenge255Bias) ∧
      PMFEventBiasLE (idealLinearMaskSimulator (F := Fp) (G := G))
        (sampledLinearMaskProver W g0 g1 x q offset qPrimeCore) (4 * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound 4
    (linearMaskTranscriptFromTape W g0 g1 x q offset qPrimeCore)
  rw [uniformTapeLinearMask_eq_idealProver,
    idealLinearMask_simulation_capstone W g0 g1 x q offset qPrimeCore hW hq] at h
  exact h

end Zcash.Snark.ZeroKnowledge
