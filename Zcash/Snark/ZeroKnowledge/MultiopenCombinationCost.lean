import Zcash.Snark.ZeroKnowledge.MultiopenAssembly
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Counted combination of public opening claims

The existing MSM-evaluation theorem identifies the public opening with a direct
fold over group points and scalars. This implementation counts that fold and its
input zip, retaining every challenge, point, and claimed-value access.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- One direct point/scalar update of the final opening combination. -/
def multiopenPointStepCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (challenge : F × ℕ) (state : G × F) (pair : (G × ℕ) × (F × ℕ)) : (G × F) × ℕ :=
  ((challenge.1 • state.1 + pair.1.1, state.2 * challenge.1 + pair.2.1),
    2 * challenge.2 + pair.1.2 + pair.2.2 + groupScale + groupAdd + costs.multiply + costs.add + 1)

/-- Count the complete direct combination, including truncating zip semantics and initial inputs. -/
def multiopenPointFoldCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (challenge : F × ℕ) (quotientPrime : G × ℕ) (points : List (G × ℕ))
    (values : List (F × ℕ)) (initialValue : F × ℕ) : (G × F) × ℕ :=
  let pairs := zipListCosted points values
  let result := foldlCosted (multiopenPointStepCosted costs groupAdd groupScale challenge) pairs.1
    ((quotientPrime.1, initialValue.1), quotientPrime.2 + initialValue.2 + 1)
  (result.1, pairs.2 + result.2 + 1)

/-- Erasure is the exact ordered point/scalar fold of the evaluated verifier combination. -/
theorem multiopenPointFoldCosted_result (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (challenge : F × ℕ) (quotientPrime : G × ℕ) (points : List (G × ℕ))
    (values : List (F × ℕ)) (initialValue : F × ℕ) :
    (multiopenPointFoldCosted costs groupAdd groupScale challenge quotientPrime points values initialValue).1 =
      ((points.map Prod.fst).zip (values.map Prod.fst)).foldl
        (fun state pair => (challenge.1 • state.1 + pair.1, state.2 * challenge.1 + pair.2))
        (quotientPrime.1, initialValue.1) := by
  simp only [multiopenPointFoldCosted, foldlCosted_result, multiopenPointStepCosted,
    zipListCosted_result, List.zip_map_left, List.zip_map_right, List.foldl_map, Prod.map, id_eq]

/-- The counted point fold gives the same public opening as the original symbolic MSM construction. -/
theorem multiopenPointFoldCosted_msm (urs : URS G) (costs : FieldOperationCosts)
    (groupAdd groupScale : ℕ) (challenge : F × ℕ) (quotientPrime : G × ℕ)
    (points : List (G × ℕ)) (values : List (F × ℕ)) (initialValue : F × ℕ) :
    let result := multiopenCombine challenge.1 quotientPrime.1
      (points.map (fun point => (Msm.zero urs.k F G).appendTerm 1 point.1))
      (values.map Prod.fst) initialValue.1 (Msm.zero urs.k F G)
    (multiopenPointFoldCosted costs groupAdd groupScale challenge quotientPrime points values initialValue).1 =
      (result.1.eval urs, result.2) := by
  dsimp only
  rw [multiopenPointFoldCosted_result]
  symm
  simpa only [List.map_map, Function.comp_def, Msm.eval_appendTerm, Msm.eval_zero, one_smul, zero_add] using
    multiopenCombine_evaluated urs challenge.1 quotientPrime.1
      (points.map (fun point => (Msm.zero urs.k F G).appendTerm 1 point.1))
      (values.map Prod.fst) initialValue.1

/-- Explicit full cost from complete supplied reads and the actual materialized point count. -/
theorem multiopenPointFoldCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (challenge : F × ℕ) (quotientPrime : G × ℕ) (points : List (G × ℕ))
    (values : List (F × ℕ)) (initialValue : F × ℕ) (pointRead valueRead : ℕ)
    (hpoints : ∀ point ∈ points, point.2 ≤ pointRead)
    (hvalues : ∀ value ∈ values, value.2 ≤ valueRead) :
    (multiopenPointFoldCosted costs groupAdd groupScale challenge quotientPrime points values initialValue).2 ≤
      quotientPrime.2 + initialValue.2 + 2 * points.length +
        points.length * (2 * challenge.2 + pointRead + valueRead + groupScale + groupAdd +
          costs.multiply + costs.add + 2) + 5 := by
  let pairs := zipListCosted points values
  let budget := 2 * challenge.2 + pointRead + valueRead + groupScale + groupAdd +
    costs.multiply + costs.add + 1
  have hfold := foldlCosted_cost_le_sum (multiopenPointStepCosted costs groupAdd groupScale challenge)
    pairs.1 ((quotientPrime.1, initialValue.1), quotientPrime.2 + initialValue.2 + 1)
    (fun _ => True) (fun _ => budget) trivial (fun _ _ _ _ => trivial) (fun _ _ pair hmem => by
      have hp : pair ∈ points.zip values := by simpa only [pairs, zipListCosted_result] using hmem
      have hpoint := hpoints pair.1 (List.of_mem_zip hp).1
      have hvalue := hvalues pair.2 (List.of_mem_zip hp).2
      dsimp only [multiopenPointStepCosted, budget]
      omega)
  have hzip := zipListCosted_cost_le points values
  have hsize : pairs.1.length ≤ points.length := by
    simp only [pairs, zipListCosted_result, List.length_zip]
    exact Nat.min_le_left _ _
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfold
  have hscaled := Nat.mul_le_mul_right budget hsize
  change pairs.2 + (foldlCosted (multiopenPointStepCosted costs groupAdd groupScale challenge)
    pairs.1 ((quotientPrime.1, initialValue.1), quotientPrime.2 + initialValue.2 + 1)).2 + 1 ≤ _
  change pairs.2 ≤ 2 * points.length + 1 at hzip
  dsimp only [budget] at hfold hscaled
  nlinarith

end Zcash.Snark.ZeroKnowledge
