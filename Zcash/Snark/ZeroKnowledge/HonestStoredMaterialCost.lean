import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCostBound
import Zcash.Snark.ZeroKnowledge.PlonkQuotientRowsBound
import Zcash.Snark.ZeroKnowledge.HonestJointRowsSource
import Zcash.Snark.ZeroKnowledge.HonestJointRowsBound
import Zcash.Snark.ZeroKnowledge.HonestJointRowsDimensions

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Construct all private rows and quotient pieces before producing the complete real joint view. -/
@[irreducible] def honestStoredMaterialCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (preIpa : List Fp) (ipaTape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  let material := plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa
  let rows := storedRowReadersCosted read (0 : Fp) 2048 material.1.1
  let pieces := plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch instances fixed sigma rows.1
  let entries := fun i : Fin (22 * actions + 10) => getDListCosted read (0 : Fp) material.1.2.2 i.val
  let joint := honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale generators W U
    instances fixed sigma rows.1 pieces.1 entries ch (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2) ipaTape
  (joint.1, material.2 + rows.2 + pieces.2 + joint.2 + 3)

end Zcash.Snark.ZeroKnowledge
