import Zcash.Snark.ZeroKnowledge.PlonkPermutationPairCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Materialize the actual factor pairs for one original permutation chunk and row. -/
def plonkPermutationFactorRowsCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (action : Fin actions)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (chunk row : ℕ) : List (Fp × Fp) × ℕ :=
  let selected := getDListCosted read [] layout.1 chunk
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let values := mapListCosted
    (plonkPermutationPairAtPointCosted costs equal read omegaAccess instances fixed sigma rows point action) selected.1
  (values.1, layout.2 + selected.2 + point.2 + values.2 + 3)

/-- Cost erasure is the exact original packed-column factor list, including absent chunks. -/
theorem plonkPermutationFactorRowsCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (action : Fin actions)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (chunk row : ℕ) :
    (plonkPermutationFactorRowsCosted costs equal read omegaAccess
      instances fixed sigma rows action layout chunk row).1 =
      plonkPermutationFactorRows
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (rows.map (fun column r => (column r).1)) action layout.1 chunk row := by
  simp only [plonkPermutationFactorRowsCosted, mapListCosted_result,
    plonkPermutationPairAtPointCosted_result, getDListCosted_result, fieldPowerCosted_result,
    plonkPermutationFactorRows, plonkPermutationPairPolynomials, List.map_map, Function.comp_def]

/-- Materialization retains precisely one pair per selected original key entry. -/
theorem plonkPermutationFactorRowsCosted_length (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (action : Fin actions)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (chunk row : ℕ) :
    (plonkPermutationFactorRowsCosted costs equal read omegaAccess
      instances fixed sigma rows action layout chunk row).1.length = (layout.1.getD chunk []).length := by
  simp only [plonkPermutationFactorRowsCosted, mapListCosted_result,
    List.length_map, getDListCosted_result]

end Zcash.Snark.ZeroKnowledge
