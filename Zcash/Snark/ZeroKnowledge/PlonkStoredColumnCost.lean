import Zcash.Snark.ZeroKnowledge.PlonkColumnMaterializeCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Construct the next private column from stored earlier columns, charging all stored-row adapters. -/
def plonkStoredColumnCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (List Fp)) : List Fp × ℕ :=
  let readers := storedRowReadersCosted read 0 2048 history
  let column := plonkConstructStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma id readers.1
  (column.1, readers.2 + column.2 + 1)

/-- Stored-history construction gives precisely the reference column on those stored values. -/
theorem plonkStoredColumnCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges k Fp)
    (thetaRead betaRead gammaRead : ℕ) (id : PrivateColumnId actions) (history : List (List Fp)) :
    (plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead)
      (ch.gamma, gammaRead) id history).1 =
      List.ofFn (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (fun a c r => (witness a c r).1) ch id
        (history.map (fun values (row : Fin 2048) => values.getD row.val 0))) := by
  simp only [plonkStoredColumnCosted, plonkConstructStoredColumnCosted_result,
    storedRowReadersCosted_result, List.map_map, Function.comp_def, getDListCosted_result]

/-- The newly stored column has the full protocol width on every construction path. -/
theorem plonkStoredColumnCosted_length (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (List Fp)) :
    (plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).1.length = 2048 :=
  plonkConstructStoredColumnCosted_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Complete bound from stored history size and input-reader prices; no earlier column is reconstructed. -/
def plonkStoredColumnCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions columns publicRowRead witnessRead
      thetaRead betaRead gammaRead : ℕ) (stored : StoredPlonkKey) : ℕ :=
  let rowRead := publicRowRead + 4097 + read
  3 * columns + 2 +
    plonkColumnPrepareCostBudget costs node equal read omegaAccess canonicalRead compare
      actions columns rowRead thetaRead stored +
    2048 * (plonkColumnRowCostBudget costs node equal read omegaAccess actions columns rowRead
      witnessRead thetaRead betaRead gammaRead stored + 3) + 2 * 2048 * 2048 + 6

end Zcash.Snark.ZeroKnowledge
