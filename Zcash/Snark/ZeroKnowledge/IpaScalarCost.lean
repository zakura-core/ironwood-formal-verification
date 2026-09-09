import Zcash.Snark.ZeroKnowledge.IpaSimulator

/-!
# Counted public branch of the sparse IPA simulator

The full finite scan and repeated squaring decide exactly the existing scalar
simulator's public condition, including zero and exceptional challenges. Field
multiplication, inversion, and equality have explicit primitive prices. The
counter also charges reversed-index arithmetic, recursive cases, conjunctions,
and every supplied input reader's complete cost. Evaluating all entries gives
a uniform bound without an early-exit assumption.

These are structural operation costs on bounded-width indices and field values.
The caller must justify the primitive prices and reader bounds for its input
representation. This component does not by itself bound the complete simulator.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Scan every finite input, retaining each reader's complete cost. -/
def allFinCosted : {count : ℕ} → (Fin count → Bool × ℕ) → Bool × ℕ
  | 0, _ => (true, 1)
  | count + 1, read =>
    let first := read 0
    let rest := allFinCosted (count := count) fun index =>
      let value := read index.succ
      (value.1, value.2 + 1)
    (first.1 && rest.1, first.2 + rest.2 + 2)

/-- The counted full scan decides the original finite universal condition. -/
theorem allFinCosted_result {count : ℕ} (read : Fin count → Bool × ℕ) :
    (allFinCosted read).1 = true ↔ ∀ index, (read index).1 = true := by
  induction count with
  | zero => simp [allFinCosted]
  | succ count ih =>
    simp only [allFinCosted, Bool.and_eq_true, ih, Fin.forall_fin_succ]

/-- Reader-index adapters, conjunctions, and recursive cases are included. -/
theorem allFinCosted_cost_le {count : ℕ} (read : Fin count → Bool × ℕ)
    (access : ℕ) (haccess : ∀ index, (read index).2 ≤ access) :
    (allFinCosted read).2 ≤ count * (access + 2) + count * count + 1 := by
  induction count generalizing access with
  | zero => simp [allFinCosted]
  | succ count ih =>
    have rest := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
      (access + 1) (fun index => Nat.add_le_add_right (haccess index.succ) 1)
    have first := haccess 0
    simp only [allFinCosted]
    nlinarith

variable {F : Type*} [Field F]

/-- Compute a power with power-of-two exponent by repeated squaring. -/
def squarePowerCosted (multiply : ℕ) (base : F) : ℕ → F × ℕ
  | 0 => (base, 1)
  | depth + 1 =>
    let previous := squarePowerCosted multiply base depth
    (previous.1 * previous.1, previous.2 + multiply + 1)

/-- Cost erasure gives exactly the powers in the sparse IPA public test. -/
theorem squarePowerCosted_result (multiply : ℕ) (base : F) (depth : ℕ) :
    (squarePowerCosted multiply base depth).1 = base ^ (2 ^ depth) := by
  induction depth with
  | zero => simp [squarePowerCosted]
  | succ depth ih =>
    simp only [squarePowerCosted, ih, pow_succ]
    rw [← pow_two, ← pow_mul]

/-- Exact repeated-squaring cost, with a price for each field multiplication. -/
theorem squarePowerCosted_cost (multiply : ℕ) (base : F) (depth : ℕ) :
    (squarePowerCosted multiply base depth).2 = depth * (multiply + 1) + 1 := by
  induction depth with
  | zero => simp [squarePowerCosted]
  | succ depth ih => simp only [squarePowerCosted, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Count the actual sparse-IPA public branch, including reversed challenge reads. -/
def chooseIpaScalarCosted [DecidableEq F] (multiply inverse equality : ℕ) {k : ℕ}
    (point : F × ℕ) (rounds : Fin k → F × ℕ) (coin : F × ℕ) : F × ℕ :=
  let test := allFinCosted fun index : Fin k =>
    let round := rounds index.rev
    let power := squarePowerCosted multiply point.1 index.val
    (decide (round.1⁻¹ = power.1), round.2 + power.2 + inverse + equality + 2)
  (if test.1 then 0 else coin.1, point.2 + coin.2 + test.2 + 1)

/-- All exceptional values follow the same branch as the existing scalar simulator. -/
theorem chooseIpaScalarCosted_result [DecidableEq F] (multiply inverse equality : ℕ) {k : ℕ}
    (point : F × ℕ) (rounds : Fin k → F × ℕ) (coin : F × ℕ) :
    (chooseIpaScalarCosted multiply inverse equality point rounds coin).1 =
      chooseIpaScalar point.1 (fun index => (rounds index).1) coin.1 := by
  have htest := allFinCosted_result (fun index : Fin k =>
    (decide ((rounds index.rev).1⁻¹ = (squarePowerCosted multiply point.1 index.val).1),
      (rounds index.rev).2 + (squarePowerCosted multiply point.1 index.val).2 + inverse + equality + 2))
  simp only [squarePowerCosted_result, decide_eq_true_eq] at htest
  unfold chooseIpaScalarCosted chooseIpaScalar
  simp only [squarePowerCosted_result, htest]

/-- The public scalar test has a quadratic round bound plus its complete input accesses. -/
theorem chooseIpaScalarCosted_cost_le [DecidableEq F] (multiply inverse equality : ℕ) {k : ℕ}
    (point : F × ℕ) (rounds : Fin k → F × ℕ) (coin : F × ℕ)
    (roundRead : ℕ) (hround : ∀ index, (rounds index).2 ≤ roundRead) :
    (chooseIpaScalarCosted multiply inverse equality point rounds coin).2 ≤
      point.2 + coin.2 +
        k * (roundRead + k * (multiply + 1) + inverse + equality + 5) + k * k + 2 := by
  have hread (index : Fin k) :
      (rounds index.rev).2 + (squarePowerCosted multiply point.1 index.val).2 + inverse + equality + 2 ≤
        roundRead + k * (multiply + 1) + inverse + equality + 3 := by
    rw [squarePowerCosted_cost]
    have hr := hround index.rev
    have hp := Nat.mul_le_mul_right (multiply + 1) index.isLt.le
    omega
  have hscan := allFinCosted_cost_le (fun index : Fin k =>
    (decide ((rounds index.rev).1⁻¹ = (squarePowerCosted multiply point.1 index.val).1),
      (rounds index.rev).2 + (squarePowerCosted multiply point.1 index.val).2 + inverse + equality + 2))
    (roundRead + k * (multiply + 1) + inverse + equality + 3) hread
  dsimp only [chooseIpaScalarCosted]
  calc
    _ ≤ point.2 + coin.2 +
        (k * (roundRead + k * (multiply + 1) + inverse + equality + 3 + 2) + k * k + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left hscan _) 1
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
