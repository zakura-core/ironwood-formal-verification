import Zcash.Snark.ZeroKnowledge.HonestTapeJointCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Actual private-material generation gives the original full joint output dimensions on every input. -/
theorem honestStoredMaterialCosted_dimensions (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (preIpa : List Fp) (ipaTape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    let view := (honestStoredMaterialCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      key generators W U instances fixed sigma witness ch preIpa ipaTape).1
    view.1.1.length = 22 * actions + 10 ∧ view.1.2.1.length = 22 * actions ∧
      (∀ column ∈ view.1.2.1, column.length = 5) ∧ view.2.messages.length = 11 := by
  let material := plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa
  let rows := storedRowReadersCosted read (0 : Fp) 2048 material.1.1
  let pieces := plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch instances fixed sigma rows.1
  let entries := fun i : Fin (22 * actions + 10) => getDListCosted read (0 : Fp) material.1.2.2 i.val
  have hm := plonkStoredMaterialFromTapeCosted_dimensions costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa
  have hl : rows.1.length = 22 * actions :=
    (storedRowReadersCosted_length read (0 : Fp) 2048 material.1.1).trans hm.1
  have h := honestJointRowsCosted_dimensions costs equal read omegaAccess groupAdd groupScale generators W U
    instances fixed sigma rows.1 pieces.1 entries ch (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2) ipaTape
  dsimp only at h
  rewrite [hl] at h
  unfold honestStoredMaterialCosted
  exact h

/-- Splitting any stored complete tape preserves all original output dimensions. -/
theorem honestTapeJointCosted_dimensions (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (tape : List Fp) :
    let view := (honestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      key generators W U instances fixed sigma witness ch tape).1
    view.1.1.length = 22 * actions + 10 ∧ view.1.2.1.length = 22 * actions ∧
      (∀ column ∈ view.1.2.1, column.length = 5) ∧ view.2.messages.length = 11 := by
  unfold honestTapeJointCosted
  exact honestStoredMaterialCosted_dimensions costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    key generators W U instances fixed sigma witness ch (splitListCosted read (148 * actions + 12) tape).1.1
    (fun i => getDListCosted read (0 : Fp) (splitListCosted read (148 * actions + 12) tape).1.2 i.val)

end Zcash.Snark.ZeroKnowledge
