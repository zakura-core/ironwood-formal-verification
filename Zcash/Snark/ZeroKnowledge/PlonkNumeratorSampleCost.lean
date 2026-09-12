import Zcash.Snark.ZeroKnowledge.PlonkNumeratorEvalBound
import Zcash.Snark.ZeroKnowledge.CosetPolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- Compute one fixed coset node with both root reads and its full exponentiation. -/
def plonkNumeratorNodeCosted (multiply omegaAccess : ℕ) (index : Fin (2 ^ 15)) : Fp × ℕ :=
  let power := fieldPowerCosted multiply (omegaOf 15) index.val
  (omegaOf 16 * power.1, 2 * omegaAccess + power.2 + multiply + 1)

/-- The computed node is the original fixed coset point. -/
theorem plonkNumeratorNodeCosted_result (multiply omegaAccess : ℕ) (index : Fin (2 ^ 15)) :
    (plonkNumeratorNodeCosted multiply omegaAccess index).1 = plonkNumeratorNode index := by
  simp only [plonkNumeratorNodeCosted, fieldPowerCosted_result, plonkNumeratorNode]

/-- Every node fits the full-domain powering budget. -/
theorem plonkNumeratorNodeCosted_cost_le (multiply omegaAccess : ℕ) (index : Fin (2 ^ 15)) :
    (plonkNumeratorNodeCosted multiply omegaAccess index).2 ≤
      2 * omegaAccess + (2 ^ 15) * (multiply + 1) + multiply + 2 := by
  have h := Nat.mul_le_mul_right (multiply + 1) (Nat.le_of_lt index.isLt)
  simp only [plonkNumeratorNodeCosted, fieldPowerCosted_cost]
  omega

/-- Compute and store a node once, then evaluate the complete actual numerator there. -/
def plonkNumeratorSampleCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (index : Fin (2 ^ 15)) : Fp × ℕ :=
  let point := plonkNumeratorNodeCosted costs.multiply omegaAccess index
  let value := plonkNumeratorEvalCosted costs node equal read omegaAccess key ch instances fixed sigma rows (point.1, 1)
  (value.1, point.2 + value.2 + 1)

/-- Every sample is the original numerator value; the internal node certificate discharges domain exclusions. -/
theorem plonkNumeratorSampleCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (index : Fin (2 ^ 15))
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    (plonkNumeratorSampleCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk) ch
      instances fixed sigma rows index).1 =
      (plonkConstraintNumerator vk (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)) (Challenges.eraseCosts ch)
        (rows.map (fun column row => (column row).1))).eval (plonkNumeratorNode index) := by
  dsimp only [plonkNumeratorSampleCosted]
  rw [plonkNumeratorNodeCosted_result]
  exact plonkNumeratorEvalCosted_result costs node equal read omegaAccess vk ch instances fixed sigma rows
    (plonkNumeratorNode index, 1) homega hn hblind (plonkNumeratorNode_off_domain index)

/-- One sample budget covers the entire fixed coset independently of sampled field values. -/
def plonkNumeratorSampleCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns baseRead yRead : ℕ) (key : StoredPlonkKey) : ℕ :=
  (2 * omegaAccess + (2 ^ 15) * (costs.multiply + 1) + costs.multiply + 2) +
    plonkNumeratorEvalCostBudget costs node equal read omegaAccess actions columns baseRead 1 yRead key + 1

/-- Complete node and numerator preparation fit a common budget at every interpolation index. -/
theorem plonkNumeratorSampleCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (index : Fin (2 ^ 15)) (baseRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ baseRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ baseRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ baseRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ baseRead)
    (hch : Challenges.ReadBound ch baseRead) :
    (plonkNumeratorSampleCosted costs node equal read omegaAccess key ch instances fixed sigma rows index).2 ≤
      plonkNumeratorSampleCostBudget costs node equal read omegaAccess actions rows.length baseRead ch.y.2 key := by
  have hp := plonkNumeratorNodeCosted_cost_le costs.multiply omegaAccess index
  have hv := plonkNumeratorEvalCosted_cost_le costs node equal read omegaAccess key ch instances fixed sigma rows
    ((plonkNumeratorNodeCosted costs.multiply omegaAccess index).1, 1) baseRead
    hinstances hfixed hsigma hrows hch
  exact Nat.add_le_add_right (Nat.add_le_add hp hv) 1

end Zcash.Snark.ZeroKnowledge
