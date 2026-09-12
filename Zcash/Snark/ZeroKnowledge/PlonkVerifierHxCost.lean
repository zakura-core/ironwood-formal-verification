import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCost
import Zcash.Snark.ZeroKnowledge.LagrangeBasisCost
import Zcash.Snark.ZeroKnowledge.QuotientEvaluationCost

/-!
# Complete inferred quotient computation

The algorithm materializes the domain power and basis values, prepares every
claim input, evaluates the complete constraint list, and performs the original
quotient fold and totalized division. All public-row, key, observation, and
challenge input costs remain explicit.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Compute the entire public inferred quotient from the original row and claim inputs. -/
def plonkVerifierHxCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (omega : Fp × ℕ) (n blinding : ℕ) (beta gamma x y delta theta : Fp × ℕ) (stride : ℕ) : Fp × ℕ :=
  let power := fieldPowerCosted costs.multiply x.1 n
  let basis := lagrangeBasisCosted costs omega n blinding (power.1, 1) x
  let constraints := plonkClaimConstraintsCosted costs node equal read omegaAccess
    instances fixed sigma views gates layout inputs tables beta gamma x delta theta stride
    (basis.1.1, 1) (basis.1.2.1, 1) (basis.1.2.2, 1)
  let entries := mapListCosted (fun value => ((value, 1), 2)) constraints.1
  let result := expectedHEvalCosted costs entries.1 y (power.1, 1)
  (result.1, x.2 + power.2 + basis.2 + constraints.2 + entries.2 + result.2 + 1)

/-- Erasure is precisely the reference verifier quotient at every challenge value. -/
theorem plonkVerifierHxCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gateCost layoutCost : ℕ) (inputCost tableCost : Fin 3 → ℕ)
    (ch : Challenges k Fp) (domainOmegaCost betaCost gammaCost xCost yCost deltaCost thetaCost : ℕ) :
    (plonkVerifierHxCosted costs node equal read omegaAccess instances fixed sigma views
      (vk.gates, gateCost) (vk.permutationChunks, layoutCost)
      (fun index => (vk.lookupInputExprs index, inputCost index))
      (fun index => (vk.lookupTableExprs index, tableCost index))
      (vk.omega, domainOmegaCost) vk.n vk.blindingFactors (ch.beta, betaCost) (ch.gamma, gammaCost)
      (ch.x, xCost) (ch.y, yCost) (vk.delta, deltaCost) (ch.theta, thetaCost) vk.chunkLen).1 =
      plonkVerifierHx vk
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        ch (privateColumnView (views.map (fun column i => (column i).1))) := by
  simp only [plonkVerifierHxCosted, expectedHEvalCosted_result, mapListCosted_result, List.map_map,
    Function.comp_def,
    plonkClaimConstraintsCosted_result costs node equal read omegaAccess vk instances fixed sigma views
      gateCost layoutCost inputCost tableCost ch betaCost gammaCost xCost deltaCost thetaCost,
    lagrangeBasisCosted_result, fieldPowerCosted_result, plonkVerifierHx, plonkPublicPolynomialsFromRows]
  rw [List.map_id']

end Zcash.Snark.ZeroKnowledge
