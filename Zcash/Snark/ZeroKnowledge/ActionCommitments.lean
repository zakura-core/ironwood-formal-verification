import Zcash.Snark.ZeroKnowledge.ActionPublicData
import Zcash.Snark.ZeroKnowledge.PlonkDerivedKey

/-!
# The actual Action compiler supplies the reference public commitments

Action's public-input and sigma commitments agree with the reference interpolants
using its proved domain and permutation count. For its full compiler-derived key,
the shape and query-layout conditions also discharge every fixed commitment.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action

/-- The existing Action public-data constructor is exactly the general compiler construction. -/
theorem actionPublicPolynomials_eq_compiler {actions : ℕ} (inputs : Fin actions → PublicInputs Fp) :
    actionPublicPolynomials inputs = plonkCompilerPublicPolynomials actionCircuit inputs := rfl

variable {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]

-- Interpolants are compared through their constructors, without expanding the domain sum.
attribute [local irreducible] polynomialCommitment rowPolynomial Zcash.Arithmetic.omegaOf

/-- The actual Action input commitment is the reference instance polynomial commitment. -/
theorem actionInstanceCommitment_eq_reference {actions : ℕ} (urs : URS G) (hurs : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (a : Fin actions) :
    actionCircuit.instanceCommitment urs inputs a 0 =
      polynomialCommitment urs.g urs.w ((actionPublicPolynomials inputs).instances a) 1 :=
  plonkKeygenInstanceCommitment actionCircuit urs actionCircuit_domainExponent_eq hurs inputs a

/-- Action's proved fifteen-column permutation count covers every reference sigma commitment. -/
theorem actionSigmaCommitment_eq_reference {actions : ℕ} (urs : URS G) (hurs : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (column : Fin 15) :
    topLevelPermutationCommitment actionCircuit urs column.val =
      polynomialCommitment urs.g urs.w ((actionPublicPolynomials inputs).sigma column) 1 := by
  apply plonkKeygenSigmaCommitment actionCircuit urs actionCircuit_domainExponent_eq hurs column
  rw [actionCircuit_permutationColumnCount_eq]
  exact column.isLt

/-- All public commitments are derived for Action's actual compiler key once its shape and layout match. -/
theorem actionCompilerPublicCommitmentsMatch {actions : ℕ} (urs : URS G) (hurs : urs.k = 11)
    (hshape : actionCircuit.shape = (plonkProofShape actions urs.k).toCircuitShape)
    (hlayout : PlonkQueryLayout (hshape ▸ actionCircuit.toVerifierKey urs))
    (inputs : Fin actions → PublicInputs Fp) :
    PlonkPublicCommitmentsMatch urs (hshape ▸ actionCircuit.toVerifierKey urs)
      (actionPublicPolynomials inputs) (actionCircuit.instanceCommitment urs inputs) :=
  plonkCompilerPublicCommitmentsMatch actionCircuit urs hurs hshape hlayout inputs

/-- Action's compiler key and public-input layout feed exactly the reference opening reconstruction. -/
theorem actionCompilerOpening_eq_public [DecidableEq G] {actions : ℕ}
    (urs : URS G) (hurs : urs.k = 11)
    (hshape : actionCircuit.shape = (plonkProofShape actions urs.k).toCircuitShape)
    (hlayout : PlonkQueryLayout (hshape ▸ actionCircuit.toVerifierKey urs))
    (inputs : Fin actions → PublicInputs Fp) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions)
    (hpoints : Function.Injective (plonkQueryPoint (Zcash.Arithmetic.omegaOf 11) ch.x)) :
    let vk := hshape ▸ actionCircuit.toVerifierKey urs
    let pub := actionPublicPolynomials inputs
    let actual := plonkVerifierOpening urs vk pub (actionCircuit.instanceCommitment urs inputs) ch view
    let reference := plonkPublicOpening urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
      (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
    (actual.1.eval urs, actual.2) = (reference.1.eval urs, reference.2) :=
  plonkCompilerOpening_eq_public actionCircuit urs hurs hshape hlayout inputs ch view hpositive hpoints

end Zcash.Snark.ZeroKnowledge
