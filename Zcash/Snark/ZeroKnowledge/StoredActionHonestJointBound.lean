import Zcash.Snark.ZeroKnowledge.StoredActionHonestJointCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Complete common access budget for actual stored Action public inputs, witness, setup, and verifier challenges. -/
def storedActionHonestInputBudget (actions challengeRead read : ℕ) : ℕ :=
  25 * actions + challengeRead + 3 * read + 4250

/-- Concrete stored representations discharge all supplied-input costs in the complete real prover. -/
theorem storedActionHonestJointCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) (key : StoredPlonkKey)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 (Fp × ℕ)) (tape : List Fp) (challengeRead : ℕ)
    (hch : Challenges.ReadBound ch challengeRead) :
    (storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) key (encodeActionWitness witness) ch tape).2 ≤
      honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length tape.length (storedActionHonestInputBudget inputs.length challengeRead read) key ch := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let access := storedActionHonestInputBudget inputs.length challengeRead read
  have hcoin : challengeRead ≤ access := by unfold access storedActionHonestInputBudget; omega
  have hread : read + 1 ≤ access := by unfold access storedActionHonestInputBudget; omega
  have hi : ∀ a r, (actionStoredInstanceRowCosted read inputs a r).2 ≤ access := by
    intro a r
    have h := actionStoredInstanceRowCosted_cost_le read inputs a r
    unfold access storedActionHonestInputBudget
    omega
  have hf : ∀ c r, (setup.fixedCosted read c r).2 ≤ access := by
    intro c r
    have h := StoredPlonkSetup.fixedCosted_encode_cost_le generators W U fixed sigma read c r
    change (setup.fixedCosted read c r).2 ≤ _ at h
    unfold access storedActionHonestInputBudget
    omega
  have hs : ∀ c r, (setup.sigmaCosted read c r).2 ≤ access := by
    intro c r
    have h := StoredPlonkSetup.sigmaCosted_encode_cost_le generators W U fixed sigma read c r
    change (setup.sigmaCosted read c r).2 ≤ _ at h
    unfold access storedActionHonestInputBudget
    omega
  have hg : ∀ i, (setup.generatorCosted read i).2 ≤ access := by
    intro i
    have h := StoredPlonkSetup.generatorCosted_encode_cost_le generators W U fixed sigma read i
    change (setup.generatorCosted read i).2 ≤ _ at h
    unfold access storedActionHonestInputBudget
    omega
  have hw : ∀ a : Fin inputs.length, ∀ c r,
      (storedActionWitnessRowCosted read (encodeActionWitness witness) a.val c r).2 ≤ access := by
    intro a c r
    have h := storedActionWitnessRowCosted_cost_le read witness a c r
    unfold access storedActionHonestInputBudget
    omega
  have hc : Challenges.ReadBound ch access := by
    rcases hch with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
    exact ⟨h0.trans hcoin,h1.trans hcoin,h2.trans hcoin,h3.trans hcoin,h4.trans hcoin,h5.trans hcoin,
      h6.trans hcoin,h7.trans hcoin,h8.trans hcoin,h9.trans hcoin,h10.trans hcoin,fun i => (h11 i).trans hcoin⟩
  unfold storedActionHonestJointCosted
  exact honestTapeJointCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale key
    (setup.generatorCosted read) (W, read + 1) (U, read + 1) (actionStoredInstanceRowCosted read inputs)
    (setup.fixedCosted read) (setup.sigmaCosted read)
    (fun a => storedActionWitnessRowCosted read (encodeActionWitness witness) a.val) ch tape access hi hf hs hw hg hread hread hc

end Zcash.Snark.ZeroKnowledge
