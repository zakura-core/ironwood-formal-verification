import Zcash.Snark.ZeroKnowledge.HonestTapeJointCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Increasing the retained pre-IPA input size preserves the complete real-material budget. -/
theorem honestStoredMaterialCostBudget_mono_tape (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions access tapeAccess : ℕ)
    (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ)) {left right : ℕ} (hle : left ≤ right) :
    honestStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions left access tapeAccess key ch ≤
    honestStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions right access tapeAccess key ch := by
  dsimp only [honestStoredMaterialCostBudget, plonkStoredMaterialCostBudget, plonkPreIpaCoinsCostBudget]
  gcongr

/-- Complete original private-tape execution budget, including the actual pre-IPA/IPA split. -/
def honestTapeJointCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions tapeLength access : ℕ)
    (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ)) : ℕ :=
  tapeLength * (read + 2) + 1 +
    honestStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions (148 * actions + 12) access (2 * tapeLength + read + 1) key ch + 2

/-- Every private tape, including totalized missing entries, satisfies the complete real-prover budget. -/
theorem honestTapeJointCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (tape : List Fp) (access : ℕ)
    (hi : ∀ a r, (instances a r).2 ≤ access) (hf : ∀ c r, (fixed c r).2 ≤ access)
    (hs : ∀ c r, (sigma c r).2 ≤ access) (hw : ∀ a c r, (witness a c r).2 ≤ access)
    (hg : ∀ i, (generators i).2 ≤ access) (hW : W.2 ≤ access) (hU : U.2 ≤ access)
    (hch : Challenges.ReadBound ch access) :
    (honestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      key generators W U instances fixed sigma witness ch tape).2 ≤
      honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        actions tape.length access key ch := by
  let parts := splitListCosted read (148 * actions + 12) tape
  have hn : parts.1.1.length ≤ 148 * actions + 12 := by
    rewrite [splitListCosted_result]
    exact List.length_take_le _ _
  have hr := (splitListCosted_lengths_le read (148 * actions + 12) tape).2
  have ht : ∀ i : Fin (ipaSampleCount 11),
      (getDListCosted read (0 : Fp) parts.1.2 i.val).2 ≤ 2 * tape.length + read + 1 := by
    intro i
    have h := getDListCosted_cost_le read (0 : Fp) parts.1.2 i.val
    change parts.1.2.length ≤ tape.length at hr
    omega
  have hj := honestStoredMaterialCosted_cost_le costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale key generators W U instances fixed sigma witness ch parts.1.1
    (fun i => getDListCosted read (0 : Fp) parts.1.2 i.val) access (2 * tape.length + read + 1)
    hi hf hs hw hg hW hU hch ht
  have hb := honestStoredMaterialCostBudget_mono_tape costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale actions access (2 * tape.length + read + 1) key ch hn
  have hp := splitListCosted_cost_le read (148 * actions + 12) tape
  unfold honestTapeJointCosted
  exact Nat.add_le_add_right (Nat.add_le_add hp (hj.trans hb)) 2

end Zcash.Snark.ZeroKnowledge
