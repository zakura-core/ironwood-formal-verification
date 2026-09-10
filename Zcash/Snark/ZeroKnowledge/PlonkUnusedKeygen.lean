import Zcash.Snark.ZeroKnowledge.PlonkUnusedSimulation
import Zcash.Snark.ZeroKnowledge.PlonkKeygenCopies

/-!
# Valid alternative reference witnesses with compiler-derived copies

The copy list is computed from the top-level compiler. Its row bound proves
that no copy touches row 2000, removing that separate footprint assumption. The
public operation-footprint bound also supplies selector placement. Original witness
validity and sigma coherence still remain explicit; the Rust witness interface and
execution behavior have not been identified with this reference relation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- A small compiler footprint gives a second valid reference witness for the actual compiled copy list. -/
theorem plonkCompilerCopies_exists_distinct_valid_witness {actions k : ℕ} {G : Type*}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hpermutation : top.permutationColumnCount = 15)
    (hused : Halo2.usedRows top.operations ≤ 1999)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (a : Fin actions) (c : Fin 10) :
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) witness copies →
      ∃ alternative : Fin actions → Fin 10 → Fin 2048 → Fp,
        PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) alternative ∧
          PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) alternative copies ∧
            witness a c plonkUnusedAdviceRow ≠ alternative a c plonkUnusedAdviceRow := by
  intro copies hcopy
  exact plonkKeygen_exists_distinct_valid_witness vk top hk hcolumns hprefix
    ((Halo2.V1_placementEnd_le_usedRows top.operations).trans hused)
    instances sigma witness hcheck hvalid copies hcopy
    (plonkKeygenCopies_avoid_unused top hpermutation (hused.trans (by decide))
      vk.permutationChunks hwidth (hused.trans (by decide))) a c

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The no-perfect-simulator result with the copy list and its unused-row property supplied by keygen. -/
theorem compilerCopiesPlonkReference_no_perfect_simulator {actions : ℕ}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hpermutation : top.permutationColumnCount = 15)
    (hused : Halo2.usedRows top.operations ≤ 1999)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := urs.k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (a : Fin actions) (c : Fin 10) :
    let copies := plonkKeygenCopies top hpermutation (hused.trans (by decide)) vk.permutationChunks hwidth
    PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) witness copies →
      ¬ ∃ simulate : PMF (PlonkFreshView actions urs.k G),
        ∀ alternative : Fin actions → Fin 10 → Fin 2048 → Fp,
          PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) alternative →
            PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) alternative copies →
              freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
                (plonkTotalColumnConstructor vk (plonkKeygenPublicPolynomials top instances sigma) alternative)
                [] vk (plonkKeygenPublicPolynomials top instances sigma) = simulate := by
  intro copies hcopy
  exact keygenPlonkReference_no_perfect_simulator urs vk top hk hcolumns hprefix
    ((Halo2.V1_placementEnd_le_usedRows top.operations).trans hused)
    instances sigma witness hcheck hvalid copies hcopy
    (plonkKeygenCopies_avoid_unused top hpermutation (hused.trans (by decide))
      vk.permutationChunks hwidth (hused.trans (by decide))) a c

end Zcash.Snark.ZeroKnowledge
