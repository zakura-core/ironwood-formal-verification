import Zcash.Snark.ZeroKnowledge.PlonkNumeratorSampleCost
import Zcash.Snark.ZeroKnowledge.CosetCoefficientCost
import Zcash.Snark.ZeroKnowledge.PlonkDegree

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- Materialize the entire actual constraint numerator from its fully counted fixed-coset evaluations. -/
def plonkNumeratorCoefficientsCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) : List Fp × ℕ :=
  cosetCoefficientsCosted costs read omegaAccess 15 (omegaOf 16, omegaAccess)
    (plonkNumeratorSampleCosted costs node equal read omegaAccess key ch instances fixed sigma rows)

/-- The stored polynomial is exactly the original numerator for every row state and every verifier challenge. -/
theorem plonkNumeratorCoefficientsCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    densePolynomial (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess
      (StoredPlonkKey.encode vk) ch instances fixed sigma rows).1 =
      plonkConstraintNumerator vk (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)) (Challenges.eraseCosts ch)
        (rows.map (fun column row => (column row).1)) := by
  obtain ⟨hi, hf, hs⟩ := plonkPublicPolynomialsFromRows_degree (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  have hd := plonkConstraintNumerator_natDegree_lt vk
    (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
      (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
    (Challenges.eraseCosts ch) (rows.map (fun column row => (column row).1)) profile hi hf hs
  apply cosetCoefficientsCosted_result costs read omegaAccess 15 (by decide)
    (omegaOf 16, omegaAccess) _ _ plonkNumeratorShift_ne_zero
    (lt_trans hd (by decide : 9 * 2048 < 2 ^ 15))
  intro index
  exact plonkNumeratorSampleCosted_result costs node equal read omegaAccess vk ch instances fixed sigma rows
    index homega hn hblind

/-- The numerator storage has a fixed polynomial-size capacity, including all trailing zeros. -/
theorem plonkNumeratorCoefficientsCosted_length (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) :
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1.length = 2 ^ 15 :=
  cosetCoefficientsCosted_length costs read omegaAccess 15 (omegaOf 16, omegaAccess) _

end Zcash.Snark.ZeroKnowledge
