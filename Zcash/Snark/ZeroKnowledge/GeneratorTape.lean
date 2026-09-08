import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite tapes from one continuing generator state

A generator step emits one word and its next private state. Tape allocation
threads that state through every word; block allocation is the same process
grouped into fixed-size attempt tapes. No probability, security, independence,
or reseeding assertion is part of these deterministic identities.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Draw a fixed number of consecutive words, retaining the resulting generator state. -/
def drawGeneratorTape {State Word : Type*} (next : State → Word × State) :
    (count : ℕ) → State → (Fin count → Word) × State
  | 0, state => (Fin.elim0, state)
  | count + 1, state =>
    let first := next state
    let later := drawGeneratorTape next count first.2
    (Fin.cons first.1 later.1, later.2)

/-- Drawing a tape advances the same state transition once per word. -/
theorem drawGeneratorTape_state {State Word : Type*} (next : State → Word × State)
    (count : ℕ) (state : State) :
    (drawGeneratorTape next count state).2 = ((fun s => (next s).2)^[count]) state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => exact ih (next state).2

/-- Every allocated word is exactly the corresponding word of the continuous generator stream. -/
theorem drawGeneratorTape_at {State Word : Type*} (next : State → Word × State)
    (count : ℕ) (state : State) (index : Fin count) :
    (drawGeneratorTape next count state).1 index =
      (next (((fun s => (next s).2)^[index.val]) state)).1 := by
  induction count generalizing state with
  | zero => exact Fin.elim0 index
  | succ count ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · rfl
    · exact ih (next state).2 index

/-- Transporting a tape index across equal capacities changes no generated word. -/
theorem drawGeneratorTape_cast {State Word : Type*} (next : State → Word × State)
    {count other : ℕ} (h : count = other) (state : State) (index : Fin count) :
    (drawGeneratorTape next other state).1 (Fin.cast h index) =
      (drawGeneratorTape next count state).1 index := by
  subst other
  rfl

/-- Allocate consecutive fixed-size attempt tapes from one generator state. -/
def drawGeneratorBlocks {State Word : Type*} (next : State → Word × State)
    (width budget : ℕ) (state : State) : (Fin budget → Fin width → Word) × State :=
  drawGeneratorTape (drawGeneratorTape next width) budget state

/-- Block allocation advances by exactly the total word capacity, without resetting between blocks. -/
theorem drawGeneratorBlocks_state {State Word : Type*} (next : State → Word × State)
    (width budget : ℕ) (state : State) :
    (drawGeneratorBlocks next width budget state).2 =
      ((fun s => (next s).2)^[budget * width]) state := by
  rw [drawGeneratorBlocks, drawGeneratorTape_state]
  have hstep : (fun s => (drawGeneratorTape next width s).2) =
      (fun s => (next s).2)^[width] := funext (drawGeneratorTape_state next width)
  rw [hstep, ← Function.iterate_mul, Nat.mul_comm width budget]

/-- Grouping a continuous stream into attempt tapes preserves every word's position. -/
theorem drawGeneratorBlocks_at {State Word : Type*} (next : State → Word × State)
    (width budget : ℕ) (state : State) (attempt : Fin budget) (slot : Fin width) :
    (drawGeneratorBlocks next width budget state).1 attempt slot =
      (next (((fun s => (next s).2)^[attempt.val * width + slot.val]) state)).1 := by
  rw [drawGeneratorBlocks, drawGeneratorTape_at, drawGeneratorTape_at]
  have hstep : (fun s => (drawGeneratorTape next width s).2) =
      (fun s => (next s).2)^[width] := funext (drawGeneratorTape_state next width)
  rw [hstep, ← Function.iterate_mul, ← Function.iterate_add_apply,
    Nat.mul_comm width attempt.val, Nat.add_comm slot.val]

end Zcash.Snark.ZeroKnowledge
