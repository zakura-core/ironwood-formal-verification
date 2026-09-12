import Zcash.Snark.ZeroKnowledge.PlonkPreIpaCoinsCostBound
import Zcash.Snark.ZeroKnowledge.PlonkTapeCausality

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Equal lengths and positionwise tape agreement imply equality of the stored values. -/
theorem TapeAgrees.ofFn {A : Type*} {m n : ℕ} {left : Fin m → A} {right : Fin n → A}
    (h : TapeAgrees left right) (hsize : m = n) : List.ofFn left = List.ofFn right := by
  subst n
  exact congrArg List.ofFn h.eq

/-- The counted decoder can use a public dummy callback while preserving every actual private coin. -/
theorem plonkPreIpaCoinsCosted_layout_result {actions : ℕ} (read : ℕ)
    (layout construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) :
    (plonkPreIpaCoinsCosted read layout (List.ofFn tape)).1 =
      (List.ofFn (plonkPreIpaCoinsEquiv construct tape).1,
        ((plonkPreIpaCoinsEquiv construct tape).2.1, List.ofFn (plonkPreIpaCoinsEquiv construct tape).2.2)) := by
  have hcount : batchedColumnSampleCount (plonkColumnBatches construct) + 12 =
      batchedColumnSampleCount (plonkColumnBatches layout) + 12 := by
    simp only [plonkColumnBatches_sample_count]
  let other : Fin (batchedColumnSampleCount (plonkColumnBatches layout) + 12) → Fp :=
    fun i => tape (Fin.cast hcount.symm i)
  have ht : TapeAgrees tape other := by
    intro i j hij
    exact congrArg tape (Fin.ext hij)
  have hl : List.ofFn tape = List.ofFn other := ht.ofFn hcount
  have hc := plonkPreIpaCoinsEquiv_constructor_irrel construct layout tape other ht
  have hr : List.ofFn (plonkPreIpaCoinsEquiv construct tape).1 =
      List.ofFn (plonkPreIpaCoinsEquiv layout other).1 := hc.1.ofFn (by
        simp only [plonkColumnSteps_row_samples])
  rw [hl, plonkPreIpaCoinsCosted_result]
  apply Prod.ext hr.symm
  exact congrArg (fun coins => (coins.1, List.ofFn coins.2)) hc.2.symm

end Zcash.Snark.ZeroKnowledge
