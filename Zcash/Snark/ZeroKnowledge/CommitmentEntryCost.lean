import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.PlonkCommitments

/-!
# Counted commitment and blinding-vector entry routing

Private columns retain the cost of constructing and searching their actual
schedule. The other slots use their original offsets, with bounded-width index
arithmetic charged explicitly. Every selected entry supplies its complete cost.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Read the original private-column slot after paying for its complete index calculation. -/
def plonkColumnEntryCosted {actions : ℕ} {α : Type*} (equal : ℕ)
    (entries : Fin (22 * actions + 10) → α × ℕ) (id : PrivateColumnId actions) : α × ℕ :=
  let index := privateColumnIndexCosted equal id
  let value := entries (Fin.castAdd 10 ⟨index.1, privateColumnIndexCosted_lt equal id⟩)
  (value.1, index.2 + value.2 + 1)

/-- Erasure reads exactly the original private-column slot. -/
theorem plonkColumnEntryCosted_result {actions : ℕ} {α : Type*} (equal : ℕ)
    (entries : Fin (22 * actions + 10) → α × ℕ) (id : PrivateColumnId actions) :
    (plonkColumnEntryCosted equal entries id).1 = plonkColumnEntry (fun index => (entries index).1) id := by
  unfold plonkColumnEntryCosted plonkColumnEntry
  apply congrArg (fun index => (entries index).1)
  apply Fin.ext
  exact privateColumnIndexCosted_result equal id

/-- The private slot bound retains both schedule traversal and the actual entry reader. -/
theorem plonkColumnEntryCosted_cost_le {actions : ℕ} {α : Type*} (equal : ℕ)
    (entries : Fin (22 * actions + 10) → α × ℕ) (id : PrivateColumnId actions)
    (access : ℕ) (hread : ∀ index, (entries index).2 ≤ access) :
    (plonkColumnEntryCosted equal entries id).2 ≤
      4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + access + 13 := by
  have hindex := privateColumnIndexCosted_cost_le equal id
  have hentry := hread (Fin.castAdd 10
    ⟨(privateColumnIndexCosted equal id).1, privateColumnIndexCosted_lt equal id⟩)
  dsimp only [plonkColumnEntryCosted]
  omega

/-- Read the linear-mask slot, retaining offset arithmetic and the selected reader. -/
def plonkLinearEntryCosted {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) : α × ℕ :=
  let value := entries (Fin.natAdd (22 * actions) 0)
  (value.1, value.2 + 3)

/-- The linear-mask router preserves the original entry. -/
theorem plonkLinearEntryCosted_result {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) :
    (plonkLinearEntryCosted entries).1 = plonkLinearEntry (fun index => (entries index).1) := rfl

/-- Complete linear-mask entry cost. -/
theorem plonkLinearEntryCosted_cost_le {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) (access : ℕ)
    (hread : ∀ index, (entries index).2 ≤ access) :
    (plonkLinearEntryCosted entries).2 ≤ access + 3 :=
  Nat.add_le_add_right (hread _) 3

/-- Read the original quotient-piece slot with all offset arithmetic counted. -/
def plonkPieceEntryCosted {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) (piece : Fin 8) : α × ℕ :=
  let value := entries (Fin.natAdd (22 * actions) (Fin.castAdd 1 piece).succ)
  (value.1, value.2 + 4)

/-- Quotient pieces retain their exact original order. -/
theorem plonkPieceEntryCosted_result {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) (piece : Fin 8) :
    (plonkPieceEntryCosted entries piece).1 = plonkPieceEntry (fun index => (entries index).1) piece := rfl

/-- Complete quotient-piece entry cost. -/
theorem plonkPieceEntryCosted_cost_le {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) (piece : Fin 8) (access : ℕ)
    (hread : ∀ index, (entries index).2 ≤ access) :
    (plonkPieceEntryCosted entries piece).2 ≤ access + 4 :=
  Nat.add_le_add_right (hread _) 4

/-- Read the final quotient-prime slot with its complete input cost. -/
def plonkQuotientPrimeEntryCosted {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) : α × ℕ :=
  let value := entries (Fin.natAdd (22 * actions) (9 : Fin 10))
  (value.1, value.2 + 3)

/-- The quotient-prime router preserves the original final slot. -/
theorem plonkQuotientPrimeEntryCosted_result {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) :
    (plonkQuotientPrimeEntryCosted entries).1 = plonkQuotientPrimeEntry (fun index => (entries index).1) := rfl

/-- Complete quotient-prime entry cost. -/
theorem plonkQuotientPrimeEntryCosted_cost_le {actions : ℕ} {α : Type*}
    (entries : Fin (22 * actions + 10) → α × ℕ) (access : ℕ)
    (hread : ∀ index, (entries index).2 ≤ access) :
    (plonkQuotientPrimeEntryCosted entries).2 ≤ access + 3 :=
  Nat.add_le_add_right (hread _) 3

end Zcash.Snark.ZeroKnowledge
