import Zcash.Snark.ZeroKnowledge.BatchedTape

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- List materialization preserves a tape split as two consecutive blocks. -/
theorem ofFn_splitTape (A : Type*) (m n : ℕ) (tape : Fin (m + n) → A) :
    List.ofFn tape = List.ofFn (splitTapeEquiv m n A tape).1 ++
      List.ofFn (splitTapeEquiv m n A tape).2 := by
  exact List.ofFn_add

/-- Joining finite tapes concatenates their materialized entries. -/
theorem ofFn_joinTape (A : Type*) (m n : ℕ) (first : Fin m → A) (rest : Fin n → A) :
    List.ofFn ((splitTapeEquiv m n A).symm (first, rest)) = List.ofFn first ++ List.ofFn rest := by
  rw [ofFn_splitTape A m n, Equiv.apply_symm_apply]

/-- The first split block is exactly the original list prefix. -/
theorem ofFn_splitTape_left (A : Type*) (m n : ℕ) (tape : Fin (m + n) → A) :
    List.ofFn (splitTapeEquiv m n A tape).1 = (List.ofFn tape).take m := by
  rw [ofFn_splitTape A m n tape]
  simp

/-- The second split block is exactly the original list suffix. -/
theorem ofFn_splitTape_right (A : Type*) (m n : ℕ) (tape : Fin (m + n) → A) :
    List.ofFn (splitTapeEquiv m n A tape).2 = (List.ofFn tape).drop m := by
  rw [ofFn_splitTape A m n tape]
  simp

/-- Materializing the canonical decoder exposes each tail followed by its own blind. -/
theorem columnCoinEquiv_cons_lists {n : ℕ} (step : ColumnStep n) (rest : List (ColumnStep n))
    (tape : Fin (columnFullSampleCount (step :: rest)) → Fp) :
    (List.ofFn (columnCoinEquiv (step :: rest) tape).1,
      List.ofFn (columnCoinEquiv (step :: rest) tape).2) =
      let first := splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp tape
      let next := splitTapeEquiv 1 (columnFullSampleCount rest) Fp first.2
      let later := columnCoinEquiv rest next.2
      (List.ofFn first.1 ++ List.ofFn later.1, next.1 0 :: List.ofFn later.2) := by
  rw [columnCoinEquiv_cons_apply]
  dsimp only
  apply Prod.ext
  · exact ofFn_joinTape Fp (n - step.firstMasked) (columnRowSampleCount rest) _ _
  · simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

end Zcash.Snark.ZeroKnowledge
