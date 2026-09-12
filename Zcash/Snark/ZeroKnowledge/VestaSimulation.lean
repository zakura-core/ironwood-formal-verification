import Zcash.Snark.ZeroKnowledge.PlonkEncoding
import Zcash.Snark.ZeroKnowledge.VestaBlinding
import Zcash.Snark.ZeroKnowledge.PlonkAttemptSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSuccess
import Zcash.Snark.ZeroKnowledge.PlonkCompilerRetry

/-!
# Concrete Vesta encodings in the compiler-derived simulation

The actual fixed-tape reference computation is observed with the specified scalar
and compressed-point encodings. Nonidentity of the URS blinding point supplies the
abstract hiding bijection. The same encodings instantiate the failure, successful
emission, and finite retained-retry theorems.

The remaining circuit/key and verifier-grouping conditions stay explicit. The
concrete Vesta module and group-cardinality facts inherit the repository's existing
Vesta point-order native certificate; the separate census names that dependency.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf URS)
open Zcash.Common
open scoped ENNReal

variable [Fintype VestaG]

/-- The canonical byte observer has the existing failure bound on the actual reference tape law. -/
theorem wideVestaPlonkReferenceAttempt_failure_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hW : urs.w ≠ 0) :
    (freshEncodedPlonkReferenceAttempt urs hk vk pub witness).toOuterMeasure
        {view | view.2.status ≠ .complete} ≤ plonkAttemptFailureBound actions := by
  rw [freshEncodedPlonkReferenceAttempt_law, PMF.toOuterMeasure_map_apply]
  exact widePlonkAttempt_failure_le urs hk (plonkTotalColumnConstructor vk pub witness) [] vk pub
    plonkPointCodec plonkScalarCodec plonkPointCodec_none_iff (vestaBlinding_bijective urs.w hW)

section Compiler

variable {actions : ℕ} {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (htopPrefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hpermutation : top.permutationColumnCount = 15)
    (hused : Halo2.usedRows top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (hindices : plonkCopySigmaIndices vk.permutationChunks)
    (hdelta : vk.delta = deltaFp) (hstride : vk.chunkLen = 7)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (instances : Fin actions → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (hmask : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true)
    (hvalid : PlonkOriginalRowsValid vk
      (plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)) witness)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hW : urs.w ≠ 0)

include hk htopPrefix hpermutation hused hfirst hwidth hindices
  hdelta hstride hqueries degree hmask hvalid homega hn hblind hchunks hpacked hW

/-- The public simulator covers the concrete encoded reference attempt with the compiler-derived budget. -/
theorem wideVestaCompilerKeygenPlonk_simulation_error_bound :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE (freshEncodedPlonkReferenceAttempt urs hk vk pub witness)
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (freshEncodedPlonkReferenceAttempt urs hk vk pub witness) (plonkSimulationErrorBound actions) := by
  intro pub copies hvalues
  simp only [freshEncodedPlonkReferenceAttempt_law]
  exact wideObservedCompilerKeygenPlonk_simulation_error_bound urs hk vk top
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked (vestaBlinding_bijective urs.w hW)
    plonkPointCodec plonkScalarCodec hvalues

/-- Successful canonical Vesta proof strings inherit the normalized compiler-derived simulation bound. -/
theorem wideVestaSuccessfulCompilerKeygenPlonk_simulation_capstone
    (hbudget : plonkCommonFailureBound actions < 1) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    let actual := freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
      (plonkTotalColumnConstructor vk pub witness) [] vk pub
    let simulate := freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub
    ∃ ha : ∃ view ∈ plonkAttemptSuccessSet plonkPointCodec plonkScalarCodec, view ∈ actual.support,
      ∃ hi : ∃ view ∈ plonkAttemptSuccessSet plonkPointCodec plonkScalarCodec, view ∈ simulate.support,
        PMFEventBiasLE (successfulPlonkView actual plonkPointCodec plonkScalarCodec ha)
            (successfulPlonkView simulate plonkPointCodec plonkScalarCodec hi) (plonkSuccessfulErrorBound actions) ∧
          PMFEventBiasLE (successfulPlonkView simulate plonkPointCodec plonkScalarCodec hi)
            (successfulPlonkView actual plonkPointCodec plonkScalarCodec ha) (plonkSuccessfulErrorBound actions) :=
  wideSuccessfulCompilerKeygenPlonk_simulation_capstone urs hk vk top
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked (vestaBlinding_bijective urs.w hW)
    plonkPointCodec plonkScalarCodec plonkPointCodec_none_iff hbudget

/-- Every finite retained history uses the actual Vesta encodings and the specified retry policy. -/
theorem wideVestaRetriedCompilerKeygenPlonk_simulation_capstone
    (hrate : plonkAttemptFailureBound actions < 1) (attempts : ℕ) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    let actual := freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
      (plonkTotalColumnConstructor vk pub witness) [] vk pub
    let simulate := freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub
    PMFEventBiasLE (observedPlonkRetries actual plonkPointCodec plonkScalarCodec attempts)
        (observedPlonkRetries simulate plonkPointCodec plonkScalarCodec attempts)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) ∧
      PMFEventBiasLE (observedPlonkRetries simulate plonkPointCodec plonkScalarCodec attempts)
        (observedPlonkRetries actual plonkPointCodec plonkScalarCodec attempts)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) :=
  wideRetriedCompilerKeygenPlonk_simulation_capstone urs hk vk top
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked (vestaBlinding_bijective urs.w hW)
    plonkPointCodec plonkScalarCodec plonkPointCodec_none_iff hrate attempts

end Compiler

end Zcash.Snark.ZeroKnowledge
