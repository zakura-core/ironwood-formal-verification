import Zcash.Snark.ZeroKnowledge.StoredActionHonestTapeJoint
import Zcash.Snark.ZeroKnowledge.HonestProverDimensions

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The full stored-bit real prover preserves all original output dimensions, including on truncated inputs. -/
theorem storedActionHonestTapeJointCosted_shape (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (bits : List Bool) :
    let view := (storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare
      groupAdd groupScale inputs setup key witness bits).1.joint
    view.1.1.length = 22 * inputs.length + 10 ∧ view.1.2.1.length = 22 * inputs.length ∧
      (∀ column ∈ view.1.2.1, column.length = 5) ∧ view.2.messages.length = 11 := by
  unfold storedActionHonestTapeJointCosted storedActionHonestJointCosted
  exact honestTapeJointCosted_dimensions costs node equal read omegaAccess canonicalRead compare groupAdd groupScale key
    (setup.generatorCosted read) (setup.w, read + 1) (setup.u, read + 1) (actionStoredInstanceRowCosted read inputs)
    (setup.fixedCosted read) (setup.sigmaCosted read) (fun a => storedActionWitnessRowCosted read witness a.val)
    (storedPlonkProverTapesCosted inputs.length read bits).1.challenges
    (storedPlonkProverTapesCosted inputs.length read bits).1.privateFields

end Zcash.Snark.ZeroKnowledge
