import Zcash.Snark.ZeroKnowledge.PlonkUnusedWitness
import Zcash.Snark.ZeroKnowledge.PlonkDisclosure

/-!
# A valid alternative input to the reference prover

Starting from one witness satisfying the reference gate, lookup, and copy relation,
the construction adds one to a cell in usable row 2000. The compiler placement bound,
inactive-expression certificate, and copy footprint imply that this second witness
is valid for the same key and public polynomials. Its complete reference-proof law
differs from the first, so an exact simulator cannot match every valid witness.

The public placement and copy conditions remain explicit. In particular, the typed
copy list still needs its compiler correspondence. This does not assert that the
Rust witness interface admits the modified unused cell, or that its failure/retry
behavior and encoded outputs match the total reference computation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- Every valid reference witness has another valid witness with a different cell in the unused row. -/
theorem plonkKeygen_exists_distinct_valid_witness {actions k : ℕ} {G : Type*}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) witness copies)
    (havoid : ∀ pair ∈ copies, pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000)
    (a : Fin actions) (c : Fin 10) :
    ∃ alternative : Fin actions → Fin 10 → Fin 2048 → Fp,
      PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) alternative ∧
        PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) alternative copies ∧
          witness a c plonkUnusedAdviceRow ≠ alternative a c plonkUnusedAdviceRow := by
  refine ⟨plonkUnusedWitness witness a c (witness a c plonkUnusedAdviceRow + 1), ?_, ?_, ?_⟩
  · exact plonkOriginalRowsValid_unused vk top hk hcolumns hprefix hplacement instances sigma
      witness hcheck hvalid a c _
  · exact plonkCopyWitness_unused vk _ witness copies hcopy havoid a c _
  · rw [plonkUnusedWitness_at]
    intro heq
    have hzero : (0 : Fp) = 1 := add_left_cancel (a := witness a c plonkUnusedAdviceRow)
      (by simpa only [add_zero] using heq)
    exact zero_ne_one hzero

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A satisfiable reference statement with this unused row has no exact simulator for all valid inputs. -/
theorem keygenPlonkReference_no_perfect_simulator {actions : ℕ}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := urs.k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) witness copies)
    (havoid : ∀ pair ∈ copies, pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000)
    (a : Fin actions) (c : Fin 10) :
    ¬ ∃ simulate : PMF (PlonkFreshView actions urs.k G),
      ∀ alternative : Fin actions → Fin 10 → Fin 2048 → Fp,
        PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) alternative →
          PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) alternative copies →
            freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
              (plonkTotalColumnConstructor vk (plonkKeygenPublicPolynomials top instances sigma) alternative)
              [] vk (plonkKeygenPublicPolynomials top instances sigma) = simulate := by
  obtain ⟨alternative, hvalid', hcopy', hcell⟩ :=
    plonkKeygen_exists_distinct_valid_witness vk top hk hcolumns hprefix hplacement instances sigma
      witness hcheck hvalid copies hcopy havoid a c
  rintro ⟨simulate, hexact⟩
  exact (widePlonkVerifierProver_no_common_exact_simulator urs vk
    (plonkKeygenPublicPolynomials top instances sigma) witness alternative a c
    plonkUnusedAdviceRow plonkUnusedAdviceRow_usable hcell)
      ⟨simulate, hexact witness hvalid hcopy, hexact alternative hvalid' hcopy'⟩

end Zcash.Snark.ZeroKnowledge
