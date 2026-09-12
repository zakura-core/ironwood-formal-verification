import Zcash.Snark.ZeroKnowledge.PlonkColumnReaderCost
import Zcash.Snark.ZeroKnowledge.TotalRowCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Construct and fully materialize one original totalized column before any later column reads it. -/
def plonkConstructStoredColumnCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) : List Fp × ℕ :=
  totalizeOptionalRowsCosted (plonkConstructColumnResultCosted costs node equal read omegaAccess
    canonicalRead compare stored instances fixed sigma witness theta beta gamma id history)

/-- Materialization agrees with the complete reference constructor, including its failed-sort zero fallback. -/
theorem plonkConstructStoredColumnCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges k Fp)
    (thetaRead betaRead gammaRead : ℕ) (id : PrivateColumnId actions)
    (history : List (Fin 2048 → Fp × ℕ)) :
    (plonkConstructStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead)
      (ch.gamma, gammaRead) id history).1 =
      List.ofFn (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (fun a c r => (witness a c r).1) ch id (history.map (fun column r => (column r).1))) := by
  simp only [plonkConstructStoredColumnCosted, totalizeOptionalRowsCosted_result,
    plonkConstructColumnResultCosted_result, plonkTotalColumnConstructor]

/-- Every constructed private column is a fully materialized 2048-entry row vector. -/
theorem plonkConstructStoredColumnCosted_length (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) :
    (plonkConstructStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).1.length = 2048 :=
  totalizeOptionalRowsCosted_length _

/-- The complete column budget combines dispatcher preparation, all row computations, and materialization. -/
theorem plonkConstructStoredColumnCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) (rowRead witnessRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hwitness : ∀ a c r, (witness a c r).2 ≤ witnessRead)
    (hrows : ∀ column ∈ history, ∀ r, (column r).2 ≤ rowRead) :
    (plonkConstructStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).2 ≤
      plonkColumnPrepareCostBudget costs node equal read omegaAccess canonicalRead compare
        actions history.length rowRead theta.2 stored +
      2048 * (plonkColumnRowCostBudget costs node equal read omegaAccess actions history.length rowRead
        witnessRead theta.2 beta.2 gamma.2 stored + 3) + 2 * 2048 * 2048 + 6 := by
  have hp := plonkConstructColumnResultCosted_prepare_cost_le costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma id history rowRead hinstances hfixed hrows
  have hr := plonkConstructColumnResultCosted_row_cost_le costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma id history rowRead witnessRead
    hinstances hfixed hsigma hwitness hrows
  have h := totalizeOptionalRowsCosted_cost_le _ _ hr
  change (totalizeOptionalRowsCosted _).2 ≤ _
  exact h.trans (by gcongr)

end Zcash.Snark.ZeroKnowledge
