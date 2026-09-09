import Zcash.Snark.ZeroKnowledge.CommitmentEntryCost
import Zcash.Snark.ZeroKnowledge.FieldExponentCost
import Zcash.Snark.ZeroKnowledge.PlonkPublicOpening

/-!
# Counted quotient-commitment reconstruction

The eight emitted quotient pieces are weighted by the exact original powers.
Every piece read, power multiplication, group scaling, and group addition is
counted. The construction and erasure include zero and exceptional challenges.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Reconstruct the quotient point while retaining all emitted-piece and challenge costs. -/
def collapsedQuotientPointCosted (multiply groupAdd groupScale : ℕ) {actions : ℕ}
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) : G × ℕ :=
  sumFinCosted groupAdd fun piece : Fin 8 =>
    let point := plonkPieceEntryCosted points piece
    let power := fieldPowerCosted multiply x.1 (2048 * piece.val)
    (power.1 • point.1, point.2 + x.2 + power.2 + groupScale + 2)

/-- Erasure preserves the eight original weights and commitment slots. -/
theorem collapsedQuotientPointCosted_result (multiply groupAdd groupScale : ℕ) {actions : ℕ}
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (collapsedQuotientPointCosted multiply groupAdd groupScale x points).1 =
      plonkCollapsedQuotientPoint x.1 (fun index => (points index).1) := by
  simp only [collapsedQuotientPointCosted, sumFinCosted_result, plonkPieceEntryCosted_result,
    fieldPowerCosted_result, plonkCollapsedQuotientPoint]

/-- Complete bound for the fixed eight-piece reconstruction. -/
theorem collapsedQuotientPointCosted_cost_le (multiply groupAdd groupScale : ℕ) {actions : ℕ}
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ)
    (access : ℕ) (haccess : ∀ index, (points index).2 ≤ access) :
    (collapsedQuotientPointCosted multiply groupAdd groupScale x points).2 ≤
      8 * (access + x.2 + 16384 * (multiply + 1) + groupScale + groupAdd + 8) + 65 := by
  let budget := access + x.2 + 16384 * (multiply + 1) + groupScale + 7
  have hentry (piece : Fin 8) :
      (plonkPieceEntryCosted points piece).2 + x.2 +
        (fieldPowerCosted multiply x.1 (2048 * piece.val)).2 + groupScale + 2 ≤ budget := by
    have hp := plonkPieceEntryCosted_cost_le points piece access haccess
    have hi : 2048 * piece.val ≤ 16384 := by omega
    have hx := Nat.mul_le_mul_right (multiply + 1) hi
    rw [fieldPowerCosted_cost]
    dsimp only [budget]
    omega
  have hsum := sumFinCosted_cost_le groupAdd (fun piece : Fin 8 =>
      ((fieldPowerCosted multiply x.1 (2048 * piece.val)).1 • (plonkPieceEntryCosted points piece).1,
        (plonkPieceEntryCosted points piece).2 + x.2 +
          (fieldPowerCosted multiply x.1 (2048 * piece.val)).2 + groupScale + 2)) budget hentry
  calc
    _ ≤ 8 * (budget + groupAdd + 1) + 8 * 8 + 1 := hsum
    _ = _ := by dsimp only [budget]; ring

end Zcash.Snark.ZeroKnowledge
