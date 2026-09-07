import Zcash.Circuits.Action.PlannerTrace
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSelectors
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigmaRows

/-!
# Public data and mask conditions from the actual Action circuit

The public instance rows come from Action's input layout; fixed and sigma rows
come from its compiler. The proved fourteen-column prefix and placement endpoint
1779 discharge the general selector-support conditions. Only the four initial
selector zeros remain as an Action masking premise. The key-expression mask check
is kernel-certified for both captured keys.

Action's opaque circuit package inherits the existing Pallas point-order certificate.
The concrete Action census records that dependency; no new native certificate is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Circuits.Action

/-- The remaining initial-row masking condition on the actual compiled Action selectors. -/
def ActionInitialSelectorsZero : Prop :=
  ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
    plonkKeygenFixedRows actionCircuit column 0 = 0

/-- The reference instance rows are the actual Action public-input layout, padded with zeros. -/
def actionInstanceRows {actions : ℕ} (inputs : Fin actions → PublicInputs Fp) :
    Fin actions → Fin 2048 → Fp :=
  fun a row => (actionCircuit.publicInputRows (inputs a) ⟨0⟩).getD row.val 0

/-- Each instance row contains exactly the corresponding canonical Action public-input element. -/
theorem actionInstanceRows_eq_elements {actions : ℕ} (inputs : Fin actions → PublicInputs Fp)
    (a : Fin actions) (row : Fin 2048) :
    actionInstanceRows inputs a row = (toElements (inputs a)).toList.getD row.val 0 := by
  unfold actionInstanceRows
  rw [actionCircuit_publicInputRows_zero]

/-- All public polynomials for the Action reference prover come from its public inputs and compiler. -/
def actionPublicPolynomials {actions : ℕ} (inputs : Fin actions → PublicInputs Fp) :
    PlonkPublicPolynomials actions :=
  plonkKeygenPublicPolynomials actionCircuit (actionInstanceRows inputs) (plonkKeygenSigmaRows actionCircuit)

/-- The instance polynomial agrees with Action's canonical public-input serialization at every domain row. -/
theorem actionPublicPolynomials_instances_eval {actions : ℕ} (inputs : Fin actions → PublicInputs Fp)
    (a : Fin actions) (row : Fin 2048) :
    ((actionPublicPolynomials inputs).instances a).eval (omegaOf 11 ^ row.val) =
      (toElements (inputs a)).toList.getD row.val 0 := by
  unfold actionPublicPolynomials plonkKeygenPublicPolynomials
  rw [plonkPublicPolynomialsFromRows_instances_eval, actionInstanceRows_eq_elements]

/-- Action's established prefix and placement facts reduce mask safety to its four initial selector zeros. -/
theorem action_plonkSelectorMaskingProfile {actions k : ℕ} {G : Type*}
    (hfirst : ActionInitialSelectorsZero)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true) :
    PlonkMaskingProfile vk (plonkKeygenPublicPolynomials actionCircuit instances sigma) :=
  plonkKeygenPublicPolynomials_selectorMaskingProfile actionCircuit
    actionCircuit_numFixedColumns_eq.le
    (actionCircuit_placementEnd_eq_1779.le.trans (by decide))
    hfirst instances sigma vk hcheck

/-- The same Action mask profile applies to its actual public-input and compiler polynomial construction. -/
theorem actionPublicPolynomials_maskingProfile {actions k : ℕ} {G : Type*}
    (hfirst : ActionInitialSelectorsZero) (inputs : Fin actions → PublicInputs Fp)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true) :
    PlonkMaskingProfile vk (actionPublicPolynomials inputs) :=
  action_plonkSelectorMaskingProfile hfirst (actionInstanceRows inputs) (plonkKeygenSigmaRows actionCircuit) vk hcheck

/-- The one-Action captured key's expression certificate supplies the remaining key-side mask check. -/
theorem singleAction_actionPublicPolynomials_maskingProfile
    (hfirst : ActionInitialSelectorsZero) (inputs : Fin 1 → PublicInputs Fp) :
    PlonkMaskingProfile (k := 11) Fixture.vk (actionPublicPolynomials inputs) :=
  actionPublicPolynomials_maskingProfile hfirst inputs Fixture.vk singleAction_plonkSelectorBoundary

/-- The two-Action captured key has the same compiler-derived Action mask profile. -/
theorem multiAction_actionPublicPolynomials_maskingProfile
    (hfirst : ActionInitialSelectorsZero) (inputs : Fin 2 → PublicInputs Fp) :
    PlonkMaskingProfile (k := 11) Fixture2.vk (actionPublicPolynomials inputs) :=
  actionPublicPolynomials_maskingProfile hfirst inputs Fixture2.vk multiAction_plonkSelectorBoundary

end Zcash.Snark.ZeroKnowledge
