import Zcash.Snark.ZeroKnowledge.ActionCommitments
import Zcash.Snark.ZeroKnowledge.ActionPublicInputCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkSetupCost
import Zcash.Snark.ZeroKnowledge.RowPolynomialCost

/-! # Complete construction of the original Action public-instance commitment -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
variable {G : Type} [AddCommGroup G] [Module Fp G]

/-- Construct all instance coefficients and their commitment with the original default blind of one. -/
def storedActionInstanceCommitmentCosted (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (action : Fin inputs.length) : G × ℕ :=
  rowPolynomialCommitmentCosted costs groupAdd groupScale (omegaOf 11, omegaAccess)
    (actionStoredInstanceRowCosted read inputs action) (setup.generatorCosted read)
    (setup.w, read + 1) (1, 1)

set_option maxRecDepth 10000 in
/-- Cost erasure recovers the actual compiler's public-input commitment, including its default blind. -/
theorem storedActionInstanceCommitmentCosted_result [Inhabited G]
    (costs : FieldOperationCosts) (groupAdd groupScale read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (action : Fin inputs.length) :
    (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) action).1 =
      actionCircuit.instanceCommitment ({ k := 11, g := generators, w := W, u := U } : URS G)
        (fun index : Fin inputs.length => inputs[index.val]) action 0 := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  have hrows : (fun row => (actionStoredInstanceRowCosted read inputs action row).1) =
      actionInstanceRows (fun index : Fin inputs.length => inputs[index.val]) action := by
    funext row
    exact actionStoredInstanceRowCosted_result read inputs action row
  have hg : (fun index : Fin 2048 => (setup.generatorCosted read index).1) = generators := by
    funext index
    exact StoredPlonkSetup.generatorCosted_encode_result generators W U fixed sigma read index
  have h : (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action).1 =
      polynomialCommitment (fun index : Fin 2048 => (setup.generatorCosted read index).1) W
        (rowPolynomial (omegaOf 11)
          (fun row : Fin 2048 => (actionStoredInstanceRowCosted read inputs action row).1)) 1 :=
    rowPolynomialCommitmentCosted_result costs groupAdd groupScale 11 (by decide) omegaAccess
      (actionStoredInstanceRowCosted read inputs action) (setup.generatorCosted read)
      (W, read + 1) (1, 1)
  rw [hrows, hg] at h
  rw [actionInstanceCommitment_eq_reference _ rfl]
  exact h

/-- A fixed complete instance-commitment envelope from the Action count and supplied primitive prices. -/
def storedActionInstanceCommitmentBudget (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess actions : ℕ) : ℕ :=
  2048 * (rowCoefficientCostBudget costs 2048 (25 * actions + 2 * read + 25) omegaAccess +
    (4097 + read) + groupScale + groupAdd + 2) + 2048 * 2048 + read + groupScale + groupAdd + 6

/-- Every row and generator access in the original public commitment has a concrete stored-data bound. -/
theorem storedActionInstanceCommitmentCosted_cost_le
    (costs : FieldOperationCosts) (groupAdd groupScale read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (action : Fin inputs.length) :
    (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) action).2 ≤
      storedActionInstanceCommitmentBudget costs groupAdd groupScale read omegaAccess inputs.length := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  have h : (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action).2 ≤
      2048 * (rowCoefficientCostBudget costs 2048 (25 * inputs.length + 2 * read + 25) omegaAccess +
        (4097 + read) + groupScale + groupAdd + 2) +
        2048 * 2048 + 1 + (read + 1) + groupScale + groupAdd + 2 :=
    rowPolynomialCommitmentCosted_cost_le costs groupAdd groupScale (omegaOf 11, omegaAccess)
      (actionStoredInstanceRowCosted read inputs action) (setup.generatorCosted read)
      (W, read + 1) (1, 1) (25 * inputs.length + 2 * read + 25) (4097 + read)
      (actionStoredInstanceRowCosted_cost_le read inputs action)
      (StoredPlonkSetup.generatorCosted_encode_cost_le generators W U fixed sigma read)
  change (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action).2 ≤ _
  dsimp only [storedActionInstanceCommitmentBudget]
  omega

end Zcash.Snark.ZeroKnowledge
