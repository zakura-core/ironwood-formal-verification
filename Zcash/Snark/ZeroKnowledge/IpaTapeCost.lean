import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.HonestIpaBound

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*}

/-- Read the original sparse coefficient at its prefix position. -/
def ipaAlphaTapeCosted {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) (index : Fin k) : F × ℕ :=
  let value := tape ⟨index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩
  (value.1, value.2 + 1)

/-- Read the original mask blind immediately after the sparse coefficients. -/
def ipaMaskTapeCosted {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) : F × ℕ :=
  let value := tape ⟨k, by unfold ipaSampleCount; omega⟩
  (value.1, value.2 + 1)

/-- Read both original round blinds, counting their offsets and pair construction. -/
def ipaRoundTapeCosted {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) (index : Fin k) : (F × F) × ℕ :=
  let left := tape ⟨k + 1 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩
  let right := tape ⟨k + 2 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩
  ((left.1, right.1), left.2 + right.2 + 7)

/-- The sparse reader uses exactly the original tape equivalence. -/
theorem ipaAlphaTapeCosted_result {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) (index : Fin k) :
    (ipaAlphaTapeCosted tape index).1 = (ipaTapeEquiv k F (fun i => (tape i).1)).1 index := by
  rewrite [ipaTapeEquiv_alphas]
  rfl

/-- The mask-blind reader uses exactly the original tape equivalence. -/
theorem ipaMaskTapeCosted_result {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) :
    (ipaMaskTapeCosted tape).1 = (ipaTapeEquiv k F (fun i => (tape i).1)).2.1 := by
  rewrite [ipaTapeEquiv_maskBlind]
  rfl

/-- The round reader preserves both original blind positions and their order. -/
theorem ipaRoundTapeCosted_result {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ) (index : Fin k) :
    (ipaRoundTapeCosted tape index).1 = (ipaTapeEquiv k F (fun i => (tape i).1)).2.2 index := by
  rewrite [ipaTapeEquiv_roundBlinds]
  rfl

/-- The sparse reader pays for its complete tape access. -/
theorem ipaAlphaTapeCosted_cost_le {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ)
    (access : ℕ) (ht : ∀ i, (tape i).2 ≤ access) (index : Fin k) :
    (ipaAlphaTapeCosted tape index).2 ≤ access + 1 := Nat.add_le_add_right (ht _) 1

/-- The mask-blind reader pays for its complete tape access. -/
theorem ipaMaskTapeCosted_cost_le {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ)
    (access : ℕ) (ht : ∀ i, (tape i).2 ≤ access) :
    (ipaMaskTapeCosted tape).2 ≤ access + 1 := Nat.add_le_add_right (ht _) 1

/-- The round reader pays for both tape accesses and all index arithmetic. -/
theorem ipaRoundTapeCosted_cost_le {k : ℕ} (tape : Fin (ipaSampleCount k) → F × ℕ)
    (access : ℕ) (ht : ∀ i, (tape i).2 ≤ access) (index : Fin k) :
    (ipaRoundTapeCosted tape index).2 ≤ 2 * access + 7 := by
  change (tape ⟨k + 1 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩).2 +
    (tape ⟨k + 2 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩).2 + 7 ≤ _
  have hl := ht ⟨k + 1 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩
  have hr := ht ⟨k + 2 + 2 * index.val, by unfold ipaSampleCount; have hi := index.isLt; omega⟩
  omega

end Zcash.Snark.ZeroKnowledge
