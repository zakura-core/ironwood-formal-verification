import Zcash.Snark.Soundness.Canonical.PermutationSemantics

/-!
# Copy replay commutes with an injective change of cell coordinates

The keygen merge step tests whether endpoints already share a cycle, then swaps
their images only when needed. Both operations are preserved by an injective map
that intertwines the current permutations. Induction over the ordered copy list
therefore preserves the exact permutation, rather than only its cycle partition.
-/

namespace Zcash.Snark.ZeroKnowledge

open Equiv (Perm swap)

private theorem permutation_pow_transport {α β : Type*}
    (encode : α → β) (left : Perm α) (right : Perm β)
    (hstep : ∀ cell, encode (left cell) = right (encode cell)) (n : ℕ) :
    ∀ cell, encode ((left ^ n) cell) = (right ^ n) (encode cell) := by
  induction n with
  | zero => intro cell; rfl
  | succ n ih =>
      intro cell
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hstep]

private theorem permutation_sameCycle_transport {α β : Type*} [Finite α] [Finite β]
    (encode : α → β) (hinjective : Function.Injective encode) (left : Perm α) (right : Perm β)
    (hstep : ∀ cell, encode (left cell) = right (encode cell)) (a b : α) :
    left.SameCycle a b ↔ right.SameCycle (encode a) (encode b) := by
  constructor
  · intro hcycle
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast] using
      (permutation_pow_transport encode left right hstep n a).symm.trans (congrArg encode hn)
  · intro hcycle
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast] using
      hinjective ((permutation_pow_transport encode left right hstep n a).trans hn)

private theorem permutation_swap_transport {α β : Type*} [DecidableEq α] [DecidableEq β]
    (encode : α → β) (hinjective : Function.Injective encode) (a b cell : α) :
    encode (swap a b cell) = swap (encode a) (encode b) (encode cell) := by
  simp only [Equiv.swap_apply_def, hinjective.eq_iff]
  split_ifs <;> rfl

private theorem copy_step_transport {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (encode : α → β) (hinjective : Function.Injective encode) (left : Perm α) (right : Perm β)
    (hstep : ∀ cell, encode (left cell) = right (encode cell)) (pair : α × α) (cell : α) :
    encode (PermConstruction.step left pair cell) =
      PermConstruction.step right (encode pair.1, encode pair.2) (encode cell) := by
  have hcycles := permutation_sameCycle_transport encode hinjective left right hstep pair.1 pair.2
  by_cases hcycle : left.SameCycle pair.1 pair.2
  · simpa only [PermConstruction.step, hcycle, hcycles.mp hcycle, ↓reduceIte] using hstep cell
  · have hcycle' : ¬ right.SameCycle (encode pair.1) (encode pair.2) :=
      fun h => hcycle (hcycles.mpr h)
    simp only [PermConstruction.step, hcycle, hcycle', ↓reduceIte, Equiv.Perm.mul_apply]
    rw [hstep, permutation_swap_transport encode hinjective]

private theorem copy_build_transport {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (encode : α → β) (hinjective : Function.Injective encode) (copies : List (α × α)) :
    ∀ cell, encode (PermConstruction.build copies cell) =
      PermConstruction.build (copies.map fun pair => (encode pair.1, encode pair.2)) (encode cell) := by
  induction copies with
  | nil => intro cell; rfl
  | cons pair rest ih =>
      intro cell
      exact copy_step_transport encode hinjective _ _ ih pair cell

/-- Mapping every copy endpoint through an injection preserves the exact ordered replay on its image. -/
theorem replayKeygenPermutation_map_apply {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (encode : α → β) (hinjective : Function.Injective encode) (copies : List (α × α)) (cell : α) :
    encode (replayKeygenPermutation copies cell) =
      replayKeygenPermutation (copies.map fun pair => (encode pair.1, encode pair.2)) (encode cell) := by
  simpa only [replayKeygenPermutation, List.map_reverse] using
    copy_build_transport encode hinjective copies.reverse cell

end Zcash.Snark.ZeroKnowledge
