import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Semantic decoding of the materialized private state; the counted prover uses stored readers. -/
def storedPrivateMaterial {actions : ℕ} (material : List (List Fp) × ((Fp × Fp) × List Fp)) :
    PlonkPrivateMaterial actions :=
  (storedColumnHistory 2048 material.1, material.2.1, fun i => material.2.2.getD i.val 0)

/-- Materialization preserves the entire original private state, including the inherited blind vector. -/
theorem storedPrivateMaterial_materialize {actions : ℕ} (material : PlonkPrivateMaterial actions) :
    storedPrivateMaterial (material.1.map List.ofFn, material.2.1, List.ofFn material.2.2) = material := by
  apply Prod.ext
  · simp only [storedPrivateMaterial, storedColumnHistory, List.map_map, Function.comp_def,
      storedRow_getD_ofFn, List.map_id']
  · apply Prod.ext
    · rfl
    · funext i
      exact storedRow_getD_ofFn material.2.2 i

/-- The actual generated reader family and blind reads recover the semantic stored material. -/
theorem storedPrivateMaterial_readers {actions : ℕ} (read : ℕ)
    (material : List (List Fp) × ((Fp × Fp) × List Fp)) :
    ((storedRowReadersCosted read (0 : Fp) 2048 material.1).1.map (fun column row => (column row).1),
      material.2.1, fun i : Fin (22 * actions + 10) => (getDListCosted read (0 : Fp) material.2.2 i.val).1) =
      storedPrivateMaterial material := by
  simp only [storedRowReadersCosted_result, List.map_map, Function.comp_def, getDListCosted_result,
    storedPrivateMaterial, storedColumnHistory]

end Zcash.Snark.ZeroKnowledge
