import Zcash.Snark.ZeroKnowledge.PlonkCompilerSimulation
import Zcash.Snark.ZeroKnowledge.PlonkSuccess

/-!
# Successful joint simulation with compiler-derived public data

This endpoint instantiates the conditioning theorem with the actual compiler
reference law and its existing witness-free simulator. The honest failure and
joint comparison theorems supply positive support on both sides. No success
probability or conditioned simulation property is assumed.

The bound is `2 epsilon / (1 - B)` where `B` is the honest failure bound plus
the raw simulation error. `B < 1` is kernel-certified whenever `m ≤ 65535`,
including both captured Action counts. The general endpoint keeps the numerical
inequality explicit rather than imposing that arithmetic range on the protocol.
The concrete circuit/key and verifier-grouping obligations of the raw theorem remain.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf URS)
open Zcash.Common
open scoped ENNReal

/-- Successful encoded reference proofs admit the public simulator with the explicit normalization cost. -/
theorem wideSuccessfulCompilerKeygenPlonk_simulation_capstone {actions : ℕ} {G : Type*}
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
    (hbudget : plonkCommonFailureBound actions < 1) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    let actual := freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
      (plonkTotalColumnConstructor vk pub witness) [] vk pub
    let simulate := freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub
    ∃ ha : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ actual.support,
      ∃ hi : ∃ view ∈ plonkAttemptSuccessSet pointCodec scalarCodec, view ∈ simulate.support,
        PMFEventBiasLE (successfulPlonkView actual pointCodec scalarCodec ha)
            (successfulPlonkView simulate pointCodec scalarCodec hi) (plonkSuccessfulErrorBound actions) ∧
          PMFEventBiasLE (successfulPlonkView simulate pointCodec scalarCodec hi)
            (successfulPlonkView actual pointCodec scalarCodec ha) (plonkSuccessfulErrorBound actions) := by
  intro pub copies hvalues actual simulate
  have h := wideCompilerKeygenPlonkVerifier_simulation_error_bound urs hk vk top htopK htopColumns
    htopPrefix hpermutation hused hfirst hwidth hindices hdelta hstride hqueries instances witness degree
    hmask hvalid homega hn hblind hchunks hpacked hW hvalues
  have hf := widePlonkAttempt_failure_le urs hk (plonkTotalColumnConstructor vk pub witness) [] vk pub
    pointCodec scalarCodec hcodec hW
  exact successfulPlonk_simulation_error_bound pointCodec scalarCodec h.1 h.2 hf hbudget

end Zcash.Snark.ZeroKnowledge
