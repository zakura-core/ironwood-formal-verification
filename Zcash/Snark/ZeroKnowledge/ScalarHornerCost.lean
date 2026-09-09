import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.ZeroKnowledge.PlonkOpening

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The original scalar Horner fold with each challenge access, list read, and field operation counted. -/
def scalarHornerCosted (read add multiply : ℕ) (challenge : Fp × ℕ) (values : List Fp) : Fp × ℕ :=
  foldlCosted (fun state value =>
    (state * challenge.1 + value, challenge.2 + read + add + multiply + 2)) values (0, 1)

/-- Erasure is exactly the source's scalar fold, including the zero challenge. -/
theorem scalarHornerCosted_result (read add multiply : ℕ) (challenge : Fp × ℕ) (values : List Fp) :
    (scalarHornerCosted read add multiply challenge values).1 = plonkScalarFold challenge.1 values := by
  simp only [scalarHornerCosted, foldlCosted_result, plonkScalarFold]

/-- Complete linear bound for a materialized scalar fold. -/
theorem scalarHornerCosted_cost_le (read add multiply : ℕ) (challenge : Fp × ℕ) (values : List Fp) :
    (scalarHornerCosted read add multiply challenge values).2 ≤
      values.length * (challenge.2 + read + add + multiply + 3) + 2 := by
  have h := foldlCosted_cost_le_sum
    (fun state value : Fp => (state * challenge.1 + value, challenge.2 + read + add + multiply + 2))
    values (0, 1) (fun _ => True) (fun _ => challenge.2 + read + add + multiply + 2)
    trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => le_rfl)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
  calc
    _ ≤ 1 + values.length * (challenge.2 + read + add + multiply + 2) + values.length + 1 := h
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
