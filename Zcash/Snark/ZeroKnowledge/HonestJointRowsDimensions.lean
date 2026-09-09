import Zcash.Snark.ZeroKnowledge.HonestJointRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Every input produces all commitments, five observations per row, and all eleven original IPA rounds. -/
theorem honestJointRowsCosted_dimensions (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (constant slope : Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    let view := (honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale generators W U
      instances fixed sigma rows pieces entries ch constant slope tape).1
    view.1.1.length = 22 * actions + 10 ∧ view.1.2.1.length = rows.length ∧
      (∀ column ∈ view.1.2.1, column.length = 5) ∧ view.2.messages.length = 11 := by
  let groups := plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces
    entries ch.x ch.x1 constant slope
  let qb := plonkQuotientPrimeEntry entries
  let data := storedMultiopenDataCosted costs equal read omegaAccess ch.x2 ch.x4 ch.x3 (qb.1, qb.2 + 1) groups.1
  let first := storedFirstOpeningCosted read groups.1
  unfold honestJointRowsCosted
  refine ⟨honestPlonkMaskCosted_points_length costs equal read omegaAccess groupAdd groupScale generators W
    rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope,
    honestPlonkMaskCosted_columns_length costs equal read omegaAccess groupAdd groupScale generators W
    rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope,
    honestPlonkMaskCosted_observations_width costs equal read omegaAccess groupAdd groupScale generators W
    rows pieces (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope, ?_⟩
  change (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data
    ch.x3 ch.xi ch.z ch.ipaRound tape).1.messages.length = 11
  rewrite [preparedHonestIpaCosted_result]
  exact List.length_ofFn

end Zcash.Snark.ZeroKnowledge
