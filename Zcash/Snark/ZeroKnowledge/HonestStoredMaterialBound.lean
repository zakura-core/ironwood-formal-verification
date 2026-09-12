import Zcash.Snark.ZeroKnowledge.HonestStoredMaterialCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialDimensions

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A common envelope for supplied inputs, generated rows, and the actual commitment-blind vector. -/
def honestStoredMaterialInputBudget (actions read access : ℕ) : ℕ := access + 44 * actions + read + 4099

/-- Complete private-material, quotient, commitment, multi-opening, and IPA execution budget. -/
def honestStoredMaterialCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions preIpaLength access tapeAccess : ℕ)
    (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ)) : ℕ :=
  let input := honestStoredMaterialInputBudget actions read access
  plonkStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare actions preIpaLength
    access access ch.theta.2 ch.beta.2 ch.gamma.2 key + (22 * actions) * 3 + 1 +
  plonkQuotientPiecesFromRowsCostBudget costs node equal read omegaAccess actions (22 * actions) input ch.y.2 key +
  honestJointRowsCostBudget costs equal read omegaAccess groupAdd groupScale actions (22 * actions) 8
    input input tapeAccess ch (read + 2) (read + 2) + 3

/-- The whole real prover on supplied split tapes has no opaque polynomial or private-row producer cost. -/
theorem honestStoredMaterialCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) {actions : ℕ}
    (key : StoredPlonkKey) (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ)
    (ch : Challenges 11 (Fp × ℕ)) (preIpa : List Fp) (ipaTape : Fin (ipaSampleCount 11) → Fp × ℕ)
    (access tapeAccess : ℕ) (hi : ∀ a r, (instances a r).2 ≤ access)
    (hf : ∀ c r, (fixed c r).2 ≤ access) (hs : ∀ c r, (sigma c r).2 ≤ access)
    (hw : ∀ a c r, (witness a c r).2 ≤ access) (hg : ∀ i, (generators i).2 ≤ access)
    (hW : W.2 ≤ access) (hU : U.2 ≤ access) (hch : Challenges.ReadBound ch access)
    (ht : ∀ i, (ipaTape i).2 ≤ tapeAccess) :
    (honestStoredMaterialCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      key generators W U instances fixed sigma witness ch preIpa ipaTape).2 ≤
      honestStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        actions preIpa.length access tapeAccess key ch := by
  let material := plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa
  let rows := storedRowReadersCosted read (0 : Fp) 2048 material.1.1
  let pieces := plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch instances fixed sigma rows.1
  let entries := fun i : Fin (22 * actions + 10) => getDListCosted read (0 : Fp) material.1.2.2 i.val
  let input := honestStoredMaterialInputBudget actions read access
  have ha : access ≤ input := by unfold input honestStoredMaterialInputBudget; omega
  have hd := plonkStoredMaterialFromTapeCosted_dimensions costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa
  change material.1.1.length = 22 * actions ∧ (∀ column ∈ material.1.1, column.length = 2048) ∧
    material.1.2.2.length ≤ 22 * actions + 10 at hd
  have hr : ∀ column ∈ rows.1, ∀ row, (column row).2 ≤ input := by
    intro column hcolumn row
    have h := storedRowReadersCosted_readBound read (0 : Fp) 2048 material.1.1 2048
      (fun values hvalues => (hd.2.1 values hvalues).le) column hcolumn row
    unfold input honestStoredMaterialInputBudget
    omega
  have he : ∀ i, (entries i).2 ≤ input := by
    intro i
    have h := getDListCosted_cost_le read (0 : Fp) material.1.2.2 i.val
    change (entries i).2 ≤ 2 * material.1.2.2.length + read + 1 at h
    unfold input honestStoredMaterialInputBudget
    omega
  have hc : Challenges.ReadBound ch input := by
    rcases hch with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
    exact ⟨h0.trans ha,h1.trans ha,h2.trans ha,h3.trans ha,h4.trans ha,h5.trans ha,h6.trans ha,
      h7.trans ha,h8.trans ha,h9.trans ha,h10.trans ha,fun i => (h11 i).trans ha⟩
  have hpieces : ∀ piece ∈ pieces.1, piece.length ≤ 2048 := fun piece hpiece =>
    (plonkQuotientPiecesFromRowsCosted_width costs node equal read omegaAccess key ch instances fixed sigma rows.1 piece hpiece).le
  have hrl : rows.1.length = 22 * actions :=
    (storedRowReadersCosted_length read (0 : Fp) 2048 material.1.1).trans hd.1
  have hpl : pieces.1.length = 8 := plonkQuotientPiecesFromRowsCosted_length costs node equal read omegaAccess key ch
    instances fixed sigma rows.1
  have hj := honestJointRowsCosted_cost_le costs equal read omegaAccess groupAdd groupScale generators W U
    instances fixed sigma rows.1 pieces.1 entries ch (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2)
    ipaTape input input tapeAccess (fun a r => (hi a r).trans ha) (fun c r => (hf c r).trans ha)
    (fun c r => (hs c r).trans ha) hr hpieces he (fun i => (hg i).trans ha) (hW.trans ha) (hU.trans ha) hc ht
  have hp := plonkQuotientPiecesFromRowsCosted_cost_le costs node equal read omegaAccess key ch instances fixed sigma rows.1
    input (fun a r => (hi a r).trans ha) (fun c r => (hf c r).trans ha) (fun c r => (hs c r).trans ha) hr hc
  have hm := plonkStoredMaterialFromTapeCosted_cost_le costs node equal read omegaAccess canonicalRead compare key
    instances fixed sigma witness ch.theta ch.beta ch.gamma preIpa access access hi hf hs hw
  have hrp := storedRowReadersCosted_cost_le read (0 : Fp) 2048 material.1.1
  change material.2 ≤ plonkStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare
    actions preIpa.length access access ch.theta.2 ch.beta.2 ch.gamma.2 key at hm
  change rows.2 ≤ material.1.1.length * 3 + 1 at hrp
  rewrite [hd.1] at hrp
  rewrite [hrl, hpl] at hj
  rewrite [hrl] at hp
  unfold honestStoredMaterialCosted
  change material.2 + rows.2 + pieces.2 + (honestJointRowsCosted costs equal read omegaAccess groupAdd groupScale
    generators W U instances fixed sigma rows.1 pieces.1 entries ch
      (material.1.2.1.1, read + 2) (material.1.2.1.2, read + 2) ipaTape).2 + 3 ≤ _
  unfold honestStoredMaterialCostBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hm hrp) hp) hj) 3

end Zcash.Snark.ZeroKnowledge
