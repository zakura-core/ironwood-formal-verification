import Zcash.Snark.ZeroKnowledge.PlonkOpeningMaterialBound
import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskBound
import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaBound
import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaSource
import Zcash.Snark.ZeroKnowledge.StoredFirstOpeningCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Materialized complete real view from actual rows and quotient pieces, on the original IPA suffix. -/
@[irreducible] def honestJointRowsCosted (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (ch : Challenges 11 (Fp × ℕ))
    (constant slope : Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  let groups := plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces
    entries ch.x ch.x1 constant slope
  let quotientBlind := plonkQuotientPrimeEntry entries
  let data := storedMultiopenDataCosted costs equal read omegaAccess ch.x2 ch.x4 ch.x3
    (quotientBlind.1, quotientBlind.2 + 1) groups.1
  let first := storedFirstOpeningCosted read groups.1
  let mask := honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
    (data.1.quotientPrime, read + 1) first entries ch.x ch.x3 constant slope
  let ipa := preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data
    ch.x3 ch.xi ch.z ch.ipaRound tape
  ((mask.1, ipa.1), groups.2 + mask.2 + ipa.2 + 1)

end Zcash.Snark.ZeroKnowledge
