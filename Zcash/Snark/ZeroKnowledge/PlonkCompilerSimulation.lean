import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigma
import Zcash.Snark.ZeroKnowledge.PlonkSelectorSimulation
import Zcash.Snark.ZeroKnowledge.PlonkUnusedKeygen

/-!
# Reference simulation with compiler-derived copies and sigma polynomials

The compiler supplies the ordered copy list, every sigma row, and the fixed rows.
Original gate, lookup, and copy-value validity remains the witness relation; public
sigma coherence is derived. The joint statistical bound is unchanged. The unused-row
counterexample also uses this compiler-produced public data.

The concrete Action size and initial-selector facts, matching the verifier key's
column meanings and public commitments, and instance provenance remain outside
these generic reference endpoints. Rust execution correspondence is a separate
claim, not a prerequisite for the specified protocol's simulation theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- Numerical joint simulation with fixed and sigma polynomials and copies computed by keygen. -/
theorem wideCompilerKeygenPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
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
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
    PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
    PMFEventBiasLE
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  intro pub copies hvalues
  exact wideSelectorKeygenPlonkVerifier_simulation_error_bound urs hk vk top htopPrefix
    ((Halo2.V1_placementEnd_le_usedRows top.operations).trans hused)
    hfirst instances (plonkKeygenSigmaRows top) witness degree hmask hvalid copies
    (plonkKeygenCopyWitness_of_values vk top hpermutation (hused.trans (by decide)) hwidth hindices
      hdelta hstride hqueries instances witness hvalues)
    homega hn hblind hchunks hpacked hW

/-- The unused-row separation also holds with compiler-produced sigma labels and original copy values. -/
theorem compilerSigmaPlonkReference_no_perfect_simulator {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hpermutation : top.permutationColumnCount = 15)
    (hused : Halo2.usedRows top.operations ≤ 1999)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (hindices : plonkCopySigmaIndices vk.permutationChunks)
    (hdelta : vk.delta = deltaFp) (hstride : vk.chunkLen = 7)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (instances : Fin actions → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := urs.k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk
      (plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)) witness)
    (a : Fin actions) (c : Fin 10) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    (∀ b : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) b vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) b vk.permutationChunks pair.2).1) →
      ¬ ∃ simulate : PMF (PlonkFreshView actions urs.k G),
        ∀ alternative : Fin actions → Fin 10 → Fin 2048 → Fp,
          PlonkOriginalRowsValid vk pub alternative →
            (∀ b : Fin actions, ∀ pair ∈ copies,
              (plonkCopyCellPair pub (plonkUnmaskedAdviceRows alternative) b vk.permutationChunks pair.1).1 =
                (plonkCopyCellPair pub (plonkUnmaskedAdviceRows alternative) b vk.permutationChunks pair.2).1) →
              freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
                (plonkTotalColumnConstructor vk pub alternative) [] vk pub = simulate := by
  intro pub copies hvalues
  have hcopy := plonkKeygenCopyWitness_of_values vk top hpermutation (hused.trans (by decide))
    hwidth hindices hdelta hstride hqueries instances witness hvalues
  have hnot := compilerCopiesPlonkReference_no_perfect_simulator urs vk top hk hcolumns hprefix
    hpermutation hused hwidth instances (plonkKeygenSigmaRows top) witness hcheck hvalid a c hcopy
  rintro ⟨simulate, hexact⟩
  exact hnot ⟨simulate, fun alternative hrows hcopies => hexact alternative hrows hcopies.values⟩

end Zcash.Snark.ZeroKnowledge
