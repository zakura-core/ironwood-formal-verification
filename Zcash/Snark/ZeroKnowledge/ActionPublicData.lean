import Zcash.Circuits.Action.PlannerTrace
import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigmaRows

/-!
# Public data from the actual Action circuit

The public instance rows come from Action's input layout; fixed and sigma rows
come from its compiler. The instance-row theorem connects these public inputs to
Action's canonical serialization. `ActionBoundaryProfile` proves the masking
profile from the compiler's actual fixed values and selector replacements.

Action's opaque circuit package inherits the existing Pallas point-order certificate.
The concrete Action census records that dependency; no new native certificate is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Circuits.Action

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

end Zcash.Snark.ZeroKnowledge
