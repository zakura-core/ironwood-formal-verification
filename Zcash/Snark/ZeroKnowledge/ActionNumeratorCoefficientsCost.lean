import Zcash.Snark.ZeroKnowledge.PlonkNumeratorCoefficientsBound
import Zcash.Snark.ZeroKnowledge.ActionGateDegree
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp URS)
open Zcash.Snark CompPoly

/-- The actual Action compiler discharges every domain and degree premise of numerator reconstruction. -/
theorem actionNumeratorCoefficientsCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} {G : Type} [AddCommGroup G] [Inhabited G]
    (urs : URS G) (hk : urs.k = 11) (ch : Challenges urs.k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) :
    let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
    densePolynomial (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess
      (StoredPlonkKey.encode vk) ch instances fixed sigma rows).1 =
      plonkConstraintNumerator vk (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)) (Challenges.eraseCosts ch)
        (rows.map (fun column row => (column row).1)) := by
  let packed := actionCircuit_newFixedCols_eq_fifteen
  have hd := actionReferenceKey_domain (actions := actions) urs hk packed
  exact plonkNumeratorCoefficientsCosted_result costs node equal read omegaAccess
    (actionReferenceKey (actions := actions) urs hk packed) ch instances fixed sigma rows
    (actionReferenceKey_degreeProfile (actions := actions) urs hk packed) hd.1 hd.2
    (actionReferenceKey_queryLayout (actions := actions) urs hk packed).blinding

end Zcash.Snark.ZeroKnowledge
