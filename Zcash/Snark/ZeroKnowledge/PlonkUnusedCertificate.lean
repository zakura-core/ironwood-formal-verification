import Zcash.Snark.ZeroKnowledge.PlonkUnusedSimulation
import Zcash.Snark.ZeroKnowledge.PlonkInactiveCertificate

/-!
# Valid alternative witnesses for the captured Action expressions

These specializations discharge the inactive-expression check for each captured key.
Compiler placement, original validity, and the copy footprint remain explicit; no
correspondence between the typed copy list and the compiler is assumed silently.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The one-Action captured expressions admit a distinct valid reference witness under the public bounds. -/
theorem singleAction_plonkKeygen_distinct_valid_witness
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin 1 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin 1 → Fin 10 → Fin 2048 → Fp)
    (hvalid : PlonkOriginalRowsValid (k := 11) Fixture.vk
      (plonkKeygenPublicPolynomials top instances sigma) witness)
    (copies : List (PlonkCopyCell Fixture.vk.permutationChunks × PlonkCopyCell Fixture.vk.permutationChunks))
    (hcopy : PlonkCopyWitness (k := 11) Fixture.vk
      (plonkKeygenPublicPolynomials top instances sigma) witness copies)
    (havoid : ∀ pair ∈ copies, pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000) :
    ∃ alternative : Fin 1 → Fin 10 → Fin 2048 → Fp,
      PlonkOriginalRowsValid (k := 11) Fixture.vk
          (plonkKeygenPublicPolynomials top instances sigma) alternative ∧
        PlonkCopyWitness (k := 11) Fixture.vk
          (plonkKeygenPublicPolynomials top instances sigma) alternative copies ∧
          witness 0 0 plonkUnusedAdviceRow ≠ alternative 0 0 plonkUnusedAdviceRow :=
  plonkKeygen_exists_distinct_valid_witness (k := 11) Fixture.vk top hk hcolumns hprefix
    hplacement instances sigma witness singleAction_plonkInactiveExpressions hvalid copies hcopy havoid 0 0

/-- The two-Action captured expressions admit the same change in the first Action's unused row. -/
theorem multiAction_plonkKeygen_distinct_valid_witness
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin 2 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin 2 → Fin 10 → Fin 2048 → Fp)
    (hvalid : PlonkOriginalRowsValid (k := 11) Fixture2.vk
      (plonkKeygenPublicPolynomials top instances sigma) witness)
    (copies : List (PlonkCopyCell Fixture2.vk.permutationChunks × PlonkCopyCell Fixture2.vk.permutationChunks))
    (hcopy : PlonkCopyWitness (k := 11) Fixture2.vk
      (plonkKeygenPublicPolynomials top instances sigma) witness copies)
    (havoid : ∀ pair ∈ copies, pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000) :
    ∃ alternative : Fin 2 → Fin 10 → Fin 2048 → Fp,
      PlonkOriginalRowsValid (k := 11) Fixture2.vk
          (plonkKeygenPublicPolynomials top instances sigma) alternative ∧
        PlonkCopyWitness (k := 11) Fixture2.vk
          (plonkKeygenPublicPolynomials top instances sigma) alternative copies ∧
          witness 0 0 plonkUnusedAdviceRow ≠ alternative 0 0 plonkUnusedAdviceRow :=
  plonkKeygen_exists_distinct_valid_witness (k := 11) Fixture2.vk top hk hcolumns hprefix
    hplacement instances sigma witness multiAction_plonkInactiveExpressions hvalid copies hcopy havoid 0 0

end Zcash.Snark.ZeroKnowledge
