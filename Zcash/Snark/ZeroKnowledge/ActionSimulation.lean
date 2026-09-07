import Zcash.Snark.ZeroKnowledge.ActionPublicData
import Zcash.Snark.ZeroKnowledge.VestaSimulation

/-!
# Encoded reference simulation with the actual Action public data

This specialization fixes the circuit to Action, obtains public instance rows
from its canonical input layout, and computes fixed rows, sigma rows, and copies
with its compiler. Existing Action facts discharge the configured fixed-column
prefix, permutation count, and complete operation-footprint bounds.

The four initial selector zeros remain explicit, as do the key-expression/layout
and original gate, lookup, and copy-value conditions. The theorem concerns the
encoded reference computation. `ActionCommitments` separately connects the actual
compiler key's public commitments and complete verifier opening to this public data
under its shape and query-layout conditions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- Action's canonical public inputs and compiler data instantiate the encoded Vesta reference bound. -/
theorem wideActionReference_simulation_error_bound {actions : ℕ} [Fintype VestaG]
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (hfirst : ActionInitialSelectorsZero)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (hindices : plonkCopySigmaIndices vk.permutationChunks)
    (hdelta : vk.delta = deltaFp) (hstride : vk.chunkLen = 7)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (hmask : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true)
    (hvalid : PlonkOriginalRowsValid vk (actionPublicPolynomials inputs) witness)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hW : urs.w ≠ 0) :
    let pub := actionPublicPolynomials inputs
    let copies := plonkKeygenCopies actionCircuit actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE (freshEncodedPlonkReferenceAttempt urs hk vk pub witness)
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE
        ((freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).map encodedPlonkAttempt)
        (freshEncodedPlonkReferenceAttempt urs hk vk pub witness) (plonkSimulationErrorBound actions) :=
  wideVestaCompilerKeygenPlonk_simulation_error_bound urs hk vk actionCircuit
    actionCircuit_numFixedColumns_eq.le actionCircuit_permutationColumnCount_eq
    (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide))
    hfirst hwidth hindices hdelta hstride hqueries (actionInstanceRows inputs) witness degree
    hmask hvalid homega hn hblind hchunks hpacked hW

end Zcash.Snark.ZeroKnowledge
