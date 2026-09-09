import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.Verifier.Assemble

/-!
# Counted scalar query routing

The adapters preserve the verifier's zero default for every out-of-range index.
In-range accesses and column selection retain the complete supplied reader cost.
Index comparisons and routing branches use bounded-width structural units.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Extend a finite costed reader with the exact original out-of-range zero behavior. -/
def finFnCosted {F : Type*} [Zero F] {n : ℕ} (read : Fin n → F × ℕ) (index : ℕ) : F × ℕ :=
  if h : index < n then
    let value := read ⟨index, h⟩
    (value.1, value.2 + 1)
  else (0, 1)

/-- Erasure is the verifier's actual finite-to-total query adapter. -/
theorem finFnCosted_result {F : Type*} [Zero F] {n : ℕ} (read : Fin n → F × ℕ) (index : ℕ) :
    (finFnCosted read index).1 = finFn (fun index => (read index).1) index := by
  unfold finFnCosted finFn
  split <;> rfl

/-- Both query branches retain their structural work and full in-range reader bound. -/
theorem finFnCosted_cost_le {F : Type*} [Zero F] {n : ℕ} (read : Fin n → F × ℕ)
    (access : ℕ) (hread : ∀ index, (read index).2 ≤ access) (index : ℕ) :
    (finFnCosted read index).2 ≤ access + 1 := by
  unfold finFnCosted
  split
  · have h := hread ⟨index, by assumption⟩
    dsimp only
    omega
  · omega

/-- Select the original column kind and retain the complete chosen query cost. -/
def columnResolveCosted {F : Type*} (reference : ColumnRef)
    (instanceRead advice fixed : ℕ → F × ℕ) : F × ℕ :=
  let value := match reference with
    | .advice index => advice index
    | .fixed index => fixed index
    | .instance index => instanceRead index
  (value.1, value.2 + 1)

/-- Erasure resolves exactly the original instance, advice, or fixed query. -/
theorem columnResolveCosted_result {F : Type*} (reference : ColumnRef)
    (instanceRead advice fixed : ℕ → F × ℕ) :
    (columnResolveCosted reference instanceRead advice fixed).1 =
      reference.resolve (fun index => (instanceRead index).1) (fun index => (advice index).1)
        (fun index => (fixed index).1) := by
  cases reference <;> rfl

/-- Column selection preserves complete query access bounds on all three routes. -/
theorem columnResolveCosted_cost_le {F : Type*} (reference : ColumnRef)
    (instanceRead advice fixed : ℕ → F × ℕ) (access : ℕ)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access)
    (hadvice : ∀ index, (advice index).2 ≤ access) (hfixed : ∀ index, (fixed index).2 ≤ access) :
    (columnResolveCosted reference instanceRead advice fixed).2 ≤ access + 1 := by
  cases reference with
  | advice index => exact Nat.add_le_add_right (hadvice index) 1
  | fixed index => exact Nat.add_le_add_right (hfixed index) 1
  | «instance» index => exact Nat.add_le_add_right (hinstance index) 1

end Zcash.Snark.ZeroKnowledge
