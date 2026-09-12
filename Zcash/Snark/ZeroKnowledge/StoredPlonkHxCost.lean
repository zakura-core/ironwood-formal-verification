import Zcash.Snark.ZeroKnowledge.StoredPlonkKeyCost
import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCostBound
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Snark

/-- Compute the reference quotient evaluation from the complete stored key and priced row readers. -/
def storedPlonkHxCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) : Fp × ℕ :=
  let result := plonkVerifierHxCosted costs node equal read omegaAccess instances fixed sigma views
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    (key.omega, read + 1) key.n key.blindingFactors ch.beta ch.gamma ch.x ch.y
    (key.delta, read + 1) ch.theta key.chunkLen
  (result.1, result.2 + 3 * (read + 1) + 1)

/-- The counted stored-key wrapper gives the exact original callback at all field challenges. -/
theorem storedPlonkHxCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) :
    (storedPlonkHxCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk) ch
      instances fixed sigma views).1 =
      plonkVerifierHx vk (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (Challenges.eraseCosts ch) (privateColumnView (views.map (fun column index => (column index).1))) := by
  let key := StoredPlonkKey.encode vk
  have hi : key.lookupInputCosted read = fun index =>
      (vk.lookupInputExprs index, (key.lookupInputCosted read index).2) := by
    funext index
    exact Prod.ext (StoredPlonkKey.lookupInputCosted_encode_result vk read index) rfl
  have ht : key.lookupTableCosted read = fun index =>
      (vk.lookupTableExprs index, (key.lookupTableCosted read index).2) := by
    funext index
    exact Prod.ext (StoredPlonkKey.lookupTableCosted_encode_result vk read index) rfl
  dsimp only [storedPlonkHxCosted]
  rw [hi, ht]
  exact plonkVerifierHxCosted_result costs node equal read omegaAccess vk instances fixed sigma views
    (read + 1) (read + 1) (fun index => (key.lookupInputCosted read index).2)
    (fun index => (key.lookupTableCosted read index).2) (Challenges.eraseCosts ch)
    (read + 1) ch.beta.2 ch.gamma.2 ch.x.2 ch.y.2 (read + 1) ch.theta.2

/-- The complete stored-key callback budget includes the numeric key-field reads. -/
def storedPlonkHxCostBudget (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    (actions viewCount access xAccess yAccess : ℕ) (key : StoredPlonkKey) : ℕ :=
  plonkVerifierHxCostBudget costs node equal read omegaAccess actions viewCount access xAccess yAccess
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    key.n key.blindingFactors key.chunkLen + 3 * (read + 1) + 1

/-- Explicit bounds on the eventual input readers discharge every stored-key callback cost. -/
theorem storedPlonkHxCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (access : ℕ)
    (hkey : read + 2 * key.lookupInputs.length + 2 * key.lookupTables.length + 1 ≤ access)
    (hinstances : ∀ action row, (instances action row).2 ≤ access)
    (hfixed : ∀ column row, (fixed column row).2 ≤ access)
    (hsigma : ∀ column row, (sigma column row).2 ≤ access)
    (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access)
    (hbeta : ch.beta.2 ≤ access) (hgamma : ch.gamma.2 ≤ access)
    (hx : ch.x.2 ≤ access) (htheta : ch.theta.2 ≤ access) :
    (storedPlonkHxCosted costs node equal read omegaAccess key ch instances fixed sigma views).2 ≤
      storedPlonkHxCostBudget costs node equal read omegaAccess actions views.length access ch.x.2 ch.y.2 key := by
  have hi (index : Fin 3) : (key.lookupInputCosted read index).2 ≤ access := by
    have h := key.lookupInputCosted_cost_le read index
    omega
  have ht (index : Fin 3) : (key.lookupTableCosted read index).2 ≤ access := by
    have h := key.lookupTableCosted_cost_le read index
    omega
  have h := plonkVerifierHxCosted_cost_le costs node equal read omegaAccess instances fixed sigma views
    (key.gatesCosted read) (key.layoutCosted read) (key.lookupInputCosted read) (key.lookupTableCosted read)
    (key.omega, read + 1) key.n key.blindingFactors ch.beta ch.gamma ch.x ch.y
    (key.delta, read + 1) ch.theta key.chunkLen access (by omega)
    hinstances hfixed hsigma hviews hi ht (by dsimp only; omega) hbeta hgamma hx
    (by dsimp only; omega) htheta
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

end Zcash.Snark.ZeroKnowledge
