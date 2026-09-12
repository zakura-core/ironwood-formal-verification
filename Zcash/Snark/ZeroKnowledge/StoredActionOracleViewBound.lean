import Zcash.Snark.ZeroKnowledge.StoredActionOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredJointTraceSize

/-! # A fixed bound for complete stored-bit Action oracle-view production -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Full bit-to-transcript work plus all canonical reports, byte queries, and raw reply reads. -/
def storedActionOracleViewCostBudget (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions bitLength initialLength : ℕ) (key : StoredPlonkKey) : ℕ :=
  storedActionTapeTraceCostBudget fieldCosts ipaCosts node equal read omegaAccess actions bitLength key +
    canonicalProtocolOracleViewBudget equal read 11 initialLength (72 * actions + 107) 22
      (plonkStoredTapeReadBudget actions 11 read)
      (2 * (22 + plonkSimulatorSampleCount actions 11) + read + 5) + 3

set_option maxRecDepth 10000 in
/-- The complete raw oracle view has one fixed polynomial envelope for every input tape and stopping branch. -/
theorem storedActionOracleViewCosted_cost_le_fixed
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (bits : Fin ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) → Bool)
    (initial : List (TranscriptElt Fp VestaG)) :
    (storedActionOracleViewCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits) initial).2 ≤
      storedActionOracleViewCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
        ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) initial.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) (List.ofFn bits)
  let produced := storedActionTapeTraceCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) (List.ofFn bits)
  let access := plonkStoredTapeReadBudget inputs.length 11 read
  let replyRead := 2 * (22 + plonkSimulatorSampleCount inputs.length 11) + read + 5
  let observed := canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace
  have hsize : produced.1.trace.length ≤ 72 * inputs.length + 107 := by
    have h := storedJointTraceCosted_length_le (k := 11) fieldCosts equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
    exact h.trans_eq (by omega)
  have hcount : protocolChallengeCount produced.1.trace = 22 :=
    storedJointTraceCosted_challengeCount (k := 11) fieldCosts equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
  have hread : Challenges.ReadBound produced.1.challenges access :=
    (storedPlonkSimulatorTapesCosted_readBound inputs.length 11 read (List.ofFn bits)).1
  have hreply (index : ℕ) : (storedDigestPrefixCosted 22 read produced.1.raw index).2 ≤ replyRead :=
    storedPlonkSimulatorTapesCosted_digest_cost_le inputs.length 11 read (List.ofFn bits) index
  have hv : observed.2 ≤ canonicalProtocolOracleViewBudget equal read 11 initial.length produced.1.trace.length
      (protocolChallengeCount produced.1.trace) access replyRead :=
    canonicalProtocolOracleViewCosted_cost_le equal read initial produced.1.challenges
      (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace access replyRead hread hreply
  have hvFixed : observed.2 ≤ canonicalProtocolOracleViewBudget equal read 11 initial.length
      (72 * inputs.length + 107) 22 access replyRead := hv.trans (by
    rw [hcount]
    dsimp only [canonicalProtocolOracleViewBudget]
    gcongr)
  have ht := storedActionTapeTraceCosted_cost_le_fixed fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma vk bits
  change produced.2 + observed.2 + 3 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add ht hvFixed) 3

end Zcash.Snark.ZeroKnowledge
