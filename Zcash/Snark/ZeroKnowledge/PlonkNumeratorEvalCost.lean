import Zcash.Snark.ZeroKnowledge.StoredPlonkHxCost
import Zcash.Snark.ZeroKnowledge.RowObservationCost
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.PlonkConstraints

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- The formal constraint numerator is independent of the later evaluation challenge. -/
theorem plonkConstraintNumerator_replace_x {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (point : Fp) :
    plonkConstraintNumerator vk pub { ch with x := point } rows =
      plonkConstraintNumerator vk pub ch rows := rfl

/-- Compute a numerator evaluation from the original row readers and complete stored-key callback. -/
def plonkNumeratorEvalCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) : Fp × ℕ :=
  let views := observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)) rows
  let quotient := storedPlonkHxCosted costs node equal read omegaAccess key { ch with x := point }
    instances fixed sigma views.1
  let power := fieldPowerCosted costs.multiply point.1 2048
  (quotient.1 * (power.1 - 1),
    views.2 + quotient.2 + point.2 + power.2 + costs.add + costs.negate + costs.multiply + 6)

/-- Outside the row domain, erasure is the actual original constraint numerator on every supplied row state. -/
theorem plonkNumeratorEvalCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hpoint : point.1 ^ 2048 ≠ 1) :
    (plonkNumeratorEvalCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk) ch
      instances fixed sigma rows point).1 =
      (plonkConstraintNumerator vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (Challenges.eraseCosts ch) (rows.map (fun column row => (column row).1))).eval point.1 := by
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  let ch' : Challenges k Fp := { Challenges.eraseCosts ch with x := point.1 }
  have h := plonkConstraintNumerator_eval_div vk pub ch'
    (rows.map (fun column row => (column row).1)) 0 homega hn hblind hpoint
  simp only [plonkNumeratorEvalCosted, storedPlonkHxCosted_result, fieldPowerCosted_result,
    observeColumnRowsCosted_result, observationPointCosted_result]
  change plonkVerifierHx vk pub ch' (privateColumnView
    (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) point.1 0)
      (rows.map (fun column row => (column row).1)))) * (point.1 ^ 2048 - 1) = _
  rw [← h, div_mul_cancel₀ _ (sub_ne_zero.mpr hpoint)]
  rw [show ch' = { Challenges.eraseCosts ch with x := point.1 } from rfl,
    plonkConstraintNumerator_replace_x]

end Zcash.Snark.ZeroKnowledge
