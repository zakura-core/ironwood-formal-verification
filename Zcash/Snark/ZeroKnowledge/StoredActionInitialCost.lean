import Zcash.Snark.ZeroKnowledge.StoredActionInstanceCost
import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost
import Zcash.Snark.ZeroKnowledge.ActionOracleModel

/-! # Complete construction of the actual Action oracle initialization -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- Construct each public-instance commitment and the key representative in the original absorb order. -/
def storedActionInitialCosted (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup VestaG) (vkTranscriptRepr : Fp × ℕ) :
    List (TranscriptElt Fp VestaG) × ℕ :=
  let points := absorbPoints2Costed (fun action (_column : Fin 1) =>
    storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action)
  (.scalar vkTranscriptRepr.1 :: points.1, vkTranscriptRepr.2 + points.2 + 3)

set_option maxRecDepth 10000 in
/-- The initialized transcript is exactly the public prefix used by the original Action oracle experiment. -/
theorem storedActionInitialCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp × ℕ) :
    (storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) vkTranscriptRepr).1 =
      actionOracleInitial ({ k := 11, g := generators, w := W, u := U } : URS VestaG) vkTranscriptRepr.1
        (fun index : Fin inputs.length => inputs[index.val]) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  have hfamily : (fun action (_column : Fin 1) =>
      (storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action).1) =
      (fun action (column : Fin 1) => actionCircuit.instanceCommitment urs
        (fun index : Fin inputs.length => inputs[index.val]) action column.val) := by
    funext action column
    have hcolumn : column.val = 0 := by omega
    rw [hcolumn]
    exact storedActionInstanceCommitmentCosted_result costs groupAdd groupScale read omegaAccess
      inputs generators W U fixed sigma action
  simp only [storedActionInitialCosted, absorbPoints2Costed_result, actionOracleInitial, initialTranscript]
  rw [hfamily]
  rfl

/-- The constructed public initialization contains precisely the key representative and one point per Action. -/
theorem storedActionInitialCosted_length (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup VestaG) (vkTranscriptRepr : Fp × ℕ) :
    (storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs setup vkTranscriptRepr).1.length =
      inputs.length + 1 := by
  simp only [storedActionInitialCosted, List.length_cons, absorbPoints2Costed_length, Nat.mul_one]

/-- The initialization bound retains all coefficient construction, group work, input reads, and output collection. -/
theorem storedActionInitialCosted_cost_le (costs : FieldOperationCosts)
    (groupAdd groupScale read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp × ℕ) :
    (storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) vkTranscriptRepr).2 ≤
      inputs.length * (storedActionInstanceCommitmentBudget costs groupAdd groupScale read omegaAccess inputs.length + 7) +
        inputs.length * inputs.length + vkTranscriptRepr.2 + 4 := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  have h := absorbPoints2Costed_cost_le (F := Fp)
    (fun action (_column : Fin 1) =>
      storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action)
    (storedActionInstanceCommitmentBudget costs groupAdd groupScale read omegaAccess inputs.length)
    (fun action _ => storedActionInstanceCommitmentCosted_cost_le costs groupAdd groupScale read omegaAccess
      inputs generators W U fixed sigma action)
  conv at h =>
    rhs
    norm_num [Nat.add_assoc]
  change vkTranscriptRepr.2 + (absorbPoints2Costed (F := Fp)
    (fun action (_column : Fin 1) =>
      storedActionInstanceCommitmentCosted costs groupAdd groupScale read omegaAccess inputs setup action)).2 + 3 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
