import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnCostBound
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnBudgetMono
import Zcash.Snark.ZeroKnowledge.PlonkColumnRecipesCost
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceResult
import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Execute and store all private columns from the ordered row-mask subsequence. -/
def plonkStoredColumnsFromTapeCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (tape : List Fp) : List (List Fp) × ℕ :=
  let recipes := privateColumnRecipesCosted actions
  let columns := storedColumnRowsFromTapeCosted 2048 read
    (plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma) recipes.1 [] (getDListCosted read 0 tape) 0
  (columns.1, recipes.2 + columns.2 + 1)

/-- The complete stored computation equals the reference column schedule on the identical selected tape. -/
theorem plonkStoredColumnsFromTapeCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges k Fp)
    (thetaRead betaRead gammaRead : ℕ) (tape : List Fp) :
    (plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead)
      (ch.gamma, gammaRead) tape).1 =
      (columnRowsFromTape (plonkColumnSteps (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (fun a c r => (witness a c r).1) ch)) [] (fun index => tape.getD index.val 0)).map List.ofFn := by
  let source := plonkTotalColumnConstructor vk
    (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
      (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)) (fun a c r => (witness a c r).1) ch
  let construct := plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
    (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead) (ch.gamma, gammaRead)
  have hc (id : PrivateColumnId actions) (history : List (List Fp)) :
      (construct id history).1 = List.ofFn (source id (storedColumnHistory 2048 history)) :=
    plonkStoredColumnCosted_result costs node equal read omegaAccess canonicalRead compare vk instances fixed sigma
      witness ch thetaRead betaRead gammaRead id history
  change (storedColumnRowsFromTapeCosted 2048 read construct
    (privateColumnRecipesCosted actions).1 [] (getDListCosted read 0 tape) 0).1 = _
  rw [storedColumnRowsFromTapeCosted_result 2048 read construct source hc, privateColumnRecipesCosted_steps]
  simp only [storedColumnHistory, List.map_nil, Nat.zero_add, getDListCosted_result]
  rfl

/-- All 22 columns per Action are fully materialized. -/
theorem plonkStoredColumnsFromTapeCosted_length (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ) (tape : List Fp) :
    (plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma tape).1.length = 22 * actions := by
  simp only [plonkStoredColumnsFromTapeCosted, storedColumnRowsFromTapeCosted_length, privateColumnRecipesCosted_length]

/-- Every output column preserves the protocol's full 2048-row width. -/
theorem plonkStoredColumnsFromTapeCosted_width (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ) (tape : List Fp) :
    ∀ values ∈ (plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma tape).1, values.length = 2048 :=
  storedColumnRowsFromTapeCosted_width _ _ _ _ _ _ _

end Zcash.Snark.ZeroKnowledge
