import Zcash.Snark.ZeroKnowledge.BatchedTapeLists
import Zcash.Snark.ZeroKnowledge.PlonkSampling

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Equal-size finite reindexing changes no materialized entry. -/
theorem ofFn_finCongrTape {A : Type*} {m n : ℕ} (h : m = n) (tape : Fin m → A) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl A)) tape) = List.ofFn tape := by
  subst n
  rfl

/-- The canonical pre-IPA decoder retains the two coefficients and appends all ten shared blinds. -/
theorem preIpaCoinEquiv_lists {n : ℕ} (steps : List (ColumnStep n))
    (tape : Fin (preIpaSampleCount steps) → Fp) :
    (List.ofFn (preIpaCoinEquiv steps tape).1,
      ((preIpaCoinEquiv steps tape).2.1, List.ofFn (preIpaCoinEquiv steps tape).2.2)) =
      let split := splitTapeEquiv (columnFullSampleCount steps) 12 Fp tape
      let coins := columnCoinEquiv steps split.1
      let extra := splitTapeEquiv 2 10 Fp split.2
      (List.ofFn coins.1, ((extra.1 0, extra.1 1), List.ofFn coins.2 ++ List.ofFn extra.2)) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  exact ofFn_joinTape Fp steps.length 10 _ _

/-- Batch conversion changes only column-coin positions and leaves all twelve shared words in place. -/
theorem batchedPreIpaCoinEquiv_lists {n : ℕ} (batches : List (List (ColumnStep n)))
    (tape : Fin (batchedColumnSampleCount batches + 12) → Fp) :
    (List.ofFn (preIpaCoinEquiv batches.flatten (batchedPreIpaTapeEquiv batches tape)).1,
      ((preIpaCoinEquiv batches.flatten (batchedPreIpaTapeEquiv batches tape)).2.1,
        List.ofFn (preIpaCoinEquiv batches.flatten (batchedPreIpaTapeEquiv batches tape)).2.2)) =
      let split := splitTapeEquiv (batchedColumnSampleCount batches) 12 Fp tape
      let coins := batchedColumnTapeLists batches (List.ofFn split.1)
      let extra := splitTapeEquiv 2 10 Fp split.2
      (coins.1, ((extra.1 0, extra.1 1), coins.2 ++ List.ofFn extra.2)) := by
  let split := splitTapeEquiv (batchedColumnSampleCount batches) 12 Fp tape
  have hs : splitTapeEquiv (columnFullSampleCount batches.flatten) 12 Fp
      (batchedPreIpaTapeEquiv batches tape) = (batchedToColumnTape batches split.1, split.2) := by
    change splitTapeEquiv _ _ Fp ((splitTapeEquiv _ _ Fp).symm _) = _
    exact (splitTapeEquiv _ _ Fp).apply_symm_apply _
  rw [preIpaCoinEquiv_lists]
  dsimp only
  rw [hs, batchedColumnTapeLists_result]

/-- The actual Action-indexed decoder's casts preserve the complete materialized coin record. -/
theorem plonkPreIpaCoinsEquiv_lists {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) :
    (List.ofFn (plonkPreIpaCoinsEquiv construct tape).1,
      ((plonkPreIpaCoinsEquiv construct tape).2.1, List.ofFn (plonkPreIpaCoinsEquiv construct tape).2.2)) =
      let split := splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct)) 12 Fp tape
      let coins := batchedColumnTapeLists (plonkColumnBatches construct) (List.ofFn split.1)
      let extra := splitTapeEquiv 2 10 Fp split.2
      (coins.1, ((extra.1 0, extra.1 1), coins.2 ++ List.ofFn extra.2)) := by
  trans (List.ofFn (preIpaCoinEquiv (plonkColumnBatches construct).flatten
      (batchedPreIpaTapeEquiv (plonkColumnBatches construct) tape)).1,
    ((preIpaCoinEquiv (plonkColumnBatches construct).flatten
      (batchedPreIpaTapeEquiv (plonkColumnBatches construct) tape)).2.1,
     List.ofFn (preIpaCoinEquiv (plonkColumnBatches construct).flatten
      (batchedPreIpaTapeEquiv (plonkColumnBatches construct) tape)).2.2))
  · refine Prod.ext ?_ (Prod.ext rfl ?_) <;> exact ofFn_finCongrTape _ _
  · exact batchedPreIpaCoinEquiv_lists _ _

end Zcash.Snark.ZeroKnowledge
