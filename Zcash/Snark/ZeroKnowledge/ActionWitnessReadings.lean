import Zcash.Snark.ZeroKnowledge.ActionWitnessConditions

/-!
# The exact private readings required by Action completeness

The original honest-prover preconditions inspect eight fields, six points, five
scalar/window pairs, and the first 32 auxiliary Merkle readings. Agreement on
those readings preserves the preconditions exactly. Raw Merkle decomposition
exports and unused auxiliary tail values do not occur in that predicate.

This interface suffices to transfer the application constructor's preconditions
to an extracted witness. It does not assert equality of every exported witness
field or assume that the actual constructor already supplies the agreement.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Circuits.Sinsemilla.Merkle.CalculateRoot

/-- Agreement on exactly the private readings used by the original completeness preconditions. -/
structure ActionWitnessReadAgreement (left right : PrivateWitness) : Prop where
  psiOld : left.psiOld = right.psiOld
  rhoOld : left.rhoOld = right.rhoOld
  nk : left.nk = right.nk
  vOld : left.vOld = right.vOld
  vNew : left.vNew = right.vNew
  psiNew : left.psiNew = right.psiNew
  magnitude : left.magnitude = right.magnitude
  sign : left.sign = right.sign
  cmOld : left.cmOld = right.cmOld
  gdOld : left.gdOld = right.gdOld
  akP : left.akP = right.akP
  pkdOld : left.pkdOld = right.pkdOld
  gdNew : left.gdNew = right.gdNew
  pkdNew : left.pkdNew = right.pkdNew
  rcv : left.rcv = right.rcv
  alpha : left.alpha = right.alpha
  rivk : left.rivk = right.rivk
  rcmOld : left.rcmOld = right.rcmOld
  rcmNew : left.rcmNew = right.rcmNew
  merklePath : ∀ index, index < 32 → left.merklePath index = right.merklePath index

/-- The original honest-prover preconditions depend only on these exact readings. -/
theorem ActionWitnessReadAgreement.proverAssumptions_iff
    {left right : PrivateWitness} (agreement : ActionWitnessReadAgreement left right)
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (inputs : PublicInputs Fp) (hints : ProverHint Fp) :
    Circuit.ProverAssumptionsPost generators bases () (combine inputs left) hints ↔
      Circuit.ProverAssumptionsPost generators bases () (combine inputs right) hints := by
  have first := pathNode_congr₂ generators bases.merkleQ 0 (k := 16)
    (fun index hindex => agreement.merklePath index (by omega))
    (congrArg Point.x agreement.cmOld)
  have second (node : Fp) := pathNode_congr generators bases.merkleQ 16 node 16
    (w := fun index => left.merklePath (16 + index))
    (w' := fun index => right.merklePath (16 + index))
    (fun index hindex => agreement.merklePath (16 + index) (by omega))
  simp only [Circuit.ProverAssumptionsPost, Circuit.ProverAssumptions,
    Circuit.ProverAssumptionsCore, combine]
  rw [first]
  simp only [second, agreement.psiOld, agreement.rhoOld, agreement.nk,
    agreement.vOld, agreement.vNew, agreement.psiNew, agreement.magnitude,
    agreement.sign, agreement.cmOld, agreement.gdOld, agreement.akP,
    agreement.pkdOld, agreement.gdNew, agreement.pkdNew, agreement.rcv,
    agreement.alpha, agreement.rivk, agreement.rcmOld, agreement.rcmNew]

/-- The application contract transfers to any extracted witness with the required original readings. -/
theorem actionWitnessConditions_proverAssumptions_of_readAgreement
    {inputs : PublicInputs Fp} {witness : PrivateWitness}
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (extracted : PrivateWitness)
    (agreement : ActionWitnessReadAgreement extracted (normalizeActionWitness witness))
    (hints : ProverHint Fp) :
    Circuit.ProverAssumptionsPost Specs.Sinsemilla.orchardGenerators orchardBases ()
      (combine inputs extracted) hints :=
  (agreement.proverAssumptions_iff _ _ inputs hints).mpr
    (actionWitnessConditions_proverAssumptions conditions hints)
end Zcash.Snark.ZeroKnowledge
