import Zcash.Snark.ZeroKnowledge.PlonkBatchPreparationCost
import Zcash.Snark.ZeroKnowledge.PreIpaTapeLists

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Decode the complete pre-IPA source block, counting all batch, coefficient, and blind work. -/
def plonkPreIpaCoinsCosted {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (List Fp × ((Fp × Fp) × List Fp)) × ℕ :=
  let first := splitListCosted read (148 * actions) tape
  let columns := plonkBatchedColumnCoinsCosted read construct first.1.1
  let coefficients := splitListCosted read 2 first.1.2
  let extra := splitListCosted read 10 coefficients.1.2
  let c0 := getDListCosted read (0 : Fp) coefficients.1.1 0
  let c1 := getDListCosted read (0 : Fp) coefficients.1.1 1
  let blinds := appendListCosted columns.1.2 extra.1.1
  ((columns.1.1, ((c0.1, c1.1), blinds.1)),
    first.2 + columns.2 + coefficients.2 + extra.2 + c0.2 + c1.2 + blinds.2 + 8)

/-- Every selected word is the corresponding word of the existing pre-IPA equivalence. -/
theorem plonkPreIpaCoinsCosted_result {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) :
    (plonkPreIpaCoinsCosted read construct (List.ofFn tape)).1 =
      (List.ofFn (plonkPreIpaCoinsEquiv construct tape).1,
        ((plonkPreIpaCoinsEquiv construct tape).2.1, List.ofFn (plonkPreIpaCoinsEquiv construct tape).2.2)) := by
  let split := splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct)) 12 Fp tape
  let extra := splitTapeEquiv 2 10 Fp split.2
  have hf : (List.ofFn tape).take (148 * actions) = List.ofFn split.1 := by
    simpa only [plonkColumnBatches_sample_count] using (ofFn_splitTape_left _ _ _ tape).symm
  have hr : (List.ofFn tape).drop (148 * actions) = List.ofFn split.2 := by
    simpa only [plonkColumnBatches_sample_count] using (ofFn_splitTape_right _ _ _ tape).symm
  have hc : (List.ofFn split.2).take 2 = List.ofFn extra.1 := (ofFn_splitTape_left Fp 2 10 split.2).symm
  have hb : (List.ofFn split.2).drop 2 = List.ofFn extra.2 := (ofFn_splitTape_right Fp 2 10 split.2).symm
  have ha : (List.ofFn extra.2).take 10 = List.ofFn extra.2 := List.take_of_length_le (by simp)
  rw [plonkPreIpaCoinsEquiv_lists]
  simp only [plonkPreIpaCoinsCosted, plonkBatchedColumnCoinsCosted, plonkColumnBatchesCosted_result,
    batchedColumnTapeListsCosted_result, splitListCosted_result, getDListCosted_result, appendListCosted_result]
  rw [hf, hr, hc, hb, ha]
  simp only [List.ofFn_succ, List.ofFn_zero, List.getD_cons_zero, List.getD_cons_succ]
  rfl

end Zcash.Snark.ZeroKnowledge
