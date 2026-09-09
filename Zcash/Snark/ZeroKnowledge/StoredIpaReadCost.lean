import Zcash.Snark.ZeroKnowledge.IpaSimulatorCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost

/-! # Complete finite readers for the materialized IPA output -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Read the stored IPA output, charging both traversals when a point pair is reused. -/
def storedIpaReadersCosted {k : ℕ} {F G : Type*} [Zero G] (read : ℕ)
    (stored : MaterializedIpaTranscript F G) : IpaTranscript k (F × ℕ) (G × ℕ) where
  maskCommitment := (stored.maskCommitment, read + 1)
  messages := fun round =>
    let pair := getDListCosted read (0, 0) stored.messages round.val
    ((pair.1.1, pair.2 + 2), (pair.1.2, pair.2 + 2))
  scalar := (stored.scalar, read + 1)
  blind := (stored.blind, read + 1)

/-- Stored readers recover every original IPA value at every valid round index. -/
theorem storedIpaReadersCosted_result {k : ℕ} {F G : Type*} [Zero G] (read : ℕ)
    (view : IpaTranscript k F G) :
    (storedIpaReadersCosted read (materializedIpaTranscript view)).eraseCosts = view := by
  simp only [storedIpaReadersCosted, IpaTranscript.eraseCosts, materializedIpaTranscript,
    getDListCosted_ofFn_result]

/-- Every stored IPA field has a concrete price from the actual message-list length. -/
theorem storedIpaReadersCosted_readBound {k : ℕ} {F G : Type*} [Zero G] (read : ℕ)
    (stored : MaterializedIpaTranscript F G) :
    let readers := storedIpaReadersCosted (k := k) read stored
    let budget := 2 * stored.messages.length + read + 3
    readers.maskCommitment.2 ≤ budget ∧
      (∀ round, (readers.messages round).1.2 ≤ budget ∧ (readers.messages round).2.2 ≤ budget) ∧
      readers.scalar.2 ≤ budget ∧ readers.blind.2 ≤ budget := by
  dsimp only [storedIpaReadersCosted]
  refine ⟨by omega, ?_, by omega, by omega⟩
  intro round
  have h := getDListCosted_cost_le read (0, 0) stored.messages round.val
  exact ⟨by omega, by omega⟩

end Zcash.Snark.ZeroKnowledge
