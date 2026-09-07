import Zcash.Snark.ZeroKnowledge.PlonkCompilerSimulation
import Zcash.Snark.ZeroKnowledge.PlonkRetry

/-!
# Joint simulation of complete retained retry histories

The compiler-derived reference prover and its public simulator use the same
policy: retry only a request for fresh randomness, and stop on completed output
or the terminal opening error. Every attempt's encoded prefix and verifier tape
are retained. For every finite attempt budget, the two-sided error is at most
`epsilon / (1 - F)`, where `F` is the honest single-attempt failure bound.

The caller uses independent private and verifier tapes across attempts and keeps
the same statement and witness. This theorem does not cover a caller retaining
mutable transcript or prover state between attempts. The reference model's
concrete circuit/key and stage-causality conditions remain explicit.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf URS)
open Zcash.Common
open scoped ENNReal

/-- The numerical joint simulator covers every retained history under the actual retry/error distinction. -/
theorem wideRetriedCompilerKeygenPlonk_simulation_capstone {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (htopK : top.domainExponent = 11) (htopColumns : 29 ≤ top.fixedColumnCount)
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
    (hW : Function.Bijective (fun r : Fp => r • urs.w))
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hrate : plonkAttemptFailureBound actions < 1) (attempts : ℕ) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    let actual := freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
      (plonkTotalColumnConstructor vk pub witness) [] vk pub
    let simulate := freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub
    PMFEventBiasLE (observedPlonkRetries actual pointCodec scalarCodec attempts)
        (observedPlonkRetries simulate pointCodec scalarCodec attempts)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) ∧
      PMFEventBiasLE (observedPlonkRetries simulate pointCodec scalarCodec attempts)
        (observedPlonkRetries actual pointCodec scalarCodec attempts)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) := by
  intro pub copies hvalues actual simulate
  have h := wideCompilerKeygenPlonkVerifier_simulation_error_bound urs hk vk top htopK htopColumns
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked hW hvalues
  have hf := widePlonkAttempt_failure_le urs hk (plonkTotalColumnConstructor vk pub witness) [] vk pub
    pointCodec scalarCodec hcodec hW
  exact observedPlonkRetries_uniform_error_bound pointCodec scalarCodec h.1 h.2 hf hrate attempts

end Zcash.Snark.ZeroKnowledge
