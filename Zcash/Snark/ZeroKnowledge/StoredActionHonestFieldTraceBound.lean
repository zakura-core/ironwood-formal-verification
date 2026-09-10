import Zcash.Snark.ZeroKnowledge.StoredActionHonestFieldTrace
import Zcash.Snark.ZeroKnowledge.StoredActionJointSize
import Zcash.Snark.ZeroKnowledge.HonestProverPriceBudget

/-! # Complete field-tape transcript bounds for the original real Action prover -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Complete joint proof construction, proof preparation, and transcript construction cost. -/
def storedActionHonestFieldTraceCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions tapeLength challengeRead : ℕ) (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ)) : ℕ :=
  let rowRead := storedActionJointInputBudget actions 0 read
  let access := routedProofReadBudget actions (22 * actions) equal read
    (storedJointProofInputBudget costs read omegaAccess rowRead challengeRead (22 * actions + 10) 11)
  let preparation := 3 * (22 * actions) + read +
    4 * (privateOpeningEvaluationCostBudget costs equal read actions (22 * actions) (read + 11) challengeRead + 1) + 65
  honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale actions tapeLength
    (storedActionHonestInputBudget actions challengeRead read) key ch +
    preparation + 8 * actions * actions + (72 * actions + 85) * access + 1300 * actions + 2199

set_option maxRecDepth 10000 in
/-- Every stored private field tape obeys the same concrete polynomial transcript-production envelope. -/
theorem storedActionHonestFieldTraceCosted_cost_le
    (costs : FieldOperationCosts) (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 (Fp × ℕ)) (challengeRead : ℕ) (tape : List Fp)
    (hread : Challenges.ReadBound ch challengeRead) :
    (storedActionHonestFieldTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (encodeActionWitness witness) ch challengeRead tape).2 ≤
      storedActionHonestFieldTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs.length
        tape.length challengeRead (StoredPlonkKey.encode vk) ch := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
    setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) ch tape
  let access := challengeRead
  let rowRead := storedActionJointInputBudget inputs.length 0 read
  have hshape : joint.1.1.1.length = 22 * inputs.length + 10 ∧
      joint.1.1.2.1.length = 22 * inputs.length ∧
      (∀ row ∈ joint.1.1.2.1, row.length = 5) ∧ joint.1.2.messages.length = 11 := by
    unfold joint storedActionHonestJointCosted
    exact honestTapeJointCosted_dimensions costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      (StoredPlonkKey.encode vk) (setup.generatorCosted read) (setup.w, read + 1) (setup.u, read + 1)
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (fun action => storedActionWitnessRowCosted read (encodeActionWitness witness) action.val) ch tape
  have hinstances (action : Fin inputs.length) (row : Fin 2048) :
      (actionStoredInstanceRowCosted read inputs action row).2 ≤ rowRead := by
    have h := actionStoredInstanceRowCosted_cost_le read inputs action row
    dsimp only [rowRead, storedActionJointInputBudget]
    omega
  have hfixed (column : Fin 29) (row : Fin 2048) : (setup.fixedCosted read column row).2 ≤ rowRead := by
    have h := StoredPlonkSetup.fixedCosted_encode_cost_le generators W U fixed sigma read column row
    dsimp only [rowRead, storedActionJointInputBudget]
    exact h.trans (by omega)
  have hsigma (column : Fin 15) (row : Fin 2048) : (setup.sigmaCosted read column row).2 ≤ rowRead := by
    have h := StoredPlonkSetup.sigmaCosted_encode_cost_le generators W U fixed sigma read column row
    dsimp only [rowRead, storedActionJointInputBudget]
    exact h.trans (by omega)
  have hrows : ∀ row ∈ joint.1.1.2.1, row.length ≤ 5 :=
    fun row hrow => (hshape.2.2.1 row hrow).le
  have ht := storedJointTraceCosted_cost_le (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (ch.x.1, access) (ch.x1.1, access) joint.1
    rowRead hinstances hfixed hsigma hrows
  dsimp only at ht
  rw [hshape.1, hshape.2.1, hshape.2.2.2] at ht
  have hj := storedActionHonestJointCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma (StoredPlonkKey.encode vk) witness ch tape challengeRead hread
  change joint.2 ≤ _ at hj
  unfold storedActionHonestFieldTraceCosted
  change joint.2 + (storedJointTraceCosted (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (ch.x.1, access) (ch.x1.1, access) joint.1).2 + 2 ≤ _
  dsimp only [storedActionHonestFieldTraceCostBudget, access, rowRead] at ht ⊢
  rw [show 72 * inputs.length + 2 * 11 + 63 = 72 * inputs.length + 85 by omega] at ht
  omega

/-- Only challenge read prices enter the complete transcript budget. -/
theorem storedActionHonestFieldTraceCostBudget_congr_prices (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions tapeLength challengeRead : ℕ)
    (key : StoredPlonkKey) (left right : Challenges 11 (Fp × ℕ))
    (hprices : Challenges.readPrices left = Challenges.readPrices right) :
    storedActionHonestFieldTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions tapeLength challengeRead key left =
    storedActionHonestFieldTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions tapeLength challengeRead key right := by
  unfold storedActionHonestFieldTraceCostBudget
  rewrite [honestTapeJointCostBudget_congr_prices costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale actions tapeLength (storedActionHonestInputBudget actions challengeRead read) key left right hprices]
  rfl

end Zcash.Snark.ZeroKnowledge
