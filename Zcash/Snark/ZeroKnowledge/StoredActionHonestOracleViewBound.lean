import Zcash.Snark.ZeroKnowledge.StoredActionHonestOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredJointTraceSize

/-! # A fixed bound for complete stored-bit Action oracle-view production -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
attribute [local irreducible] storedPlonkProverTapesCosted

/-- Full bit-to-transcript work plus all canonical reports, byte queries, and raw reply reads. -/
def storedActionHonestOracleViewCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions bitLength initialLength : ℕ) (key : StoredPlonkKey) : ℕ :=
  storedActionHonestTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale actions bitLength key +
    canonicalProtocolOracleViewBudget equal read 11 initialLength (72 * actions + 107) 22
      (storedPlonkProverTapeReadBudget actions read)
      (2 * (22 + fieldSampleCount actions) + read + 5) + 3

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- The complete raw oracle view has one fixed polynomial envelope for every input tape and stopping branch. -/
theorem storedActionHonestOracleViewCosted_cost_le_fixed
    (costs : FieldOperationCosts) (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (bits : List Bool)
    (initial : List (TranscriptElt Fp VestaG)) :
    (storedActionHonestOracleViewCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits initial).2 ≤
      storedActionHonestOracleViewCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs.length
        bits.length initial.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
    setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits
  let produced := storedActionHonestTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
    setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits
  let access := storedPlonkProverTapeReadBudget inputs.length read
  let replyRead := 2 * (22 + fieldSampleCount inputs.length) + read + 5
  let observed := canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace
  have htrace : produced.1.trace = (storedJointTraceCosted (k := 11) costs equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint).1 := by
    unfold produced storedActionHonestTraceCosted
    rfl
  have hsource : produced.1.raw = (storedPlonkProverTapesCosted inputs.length read bits).1.raw ∧
      produced.1.challenges = (storedPlonkProverTapesCosted inputs.length read bits).1.challenges := by
    unfold produced storedActionHonestTraceCosted storedActionHonestTapeJointCosted
    exact ⟨rfl, rfl⟩
  have hsize : produced.1.trace.length ≤ 72 * inputs.length + 107 := by
    rewrite [htrace]
    have h := storedJointTraceCosted_length_le (k := 11) costs equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
    exact h.trans_eq (by omega)
  have hcount : protocolChallengeCount produced.1.trace = 22 := by
    rewrite [htrace]
    exact storedJointTraceCosted_challengeCount (k := 11) costs equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
  have hread : Challenges.ReadBound produced.1.challenges access := by
    rewrite [hsource.2]
    exact storedPlonkProverTapesCosted_readBound inputs.length read bits
  have hreply (index : ℕ) : (storedDigestPrefixCosted 22 read produced.1.raw index).2 ≤ replyRead := by
    rewrite [hsource.1]
    exact storedPlonkProverTapesCosted_digest_cost_le inputs.length read bits index
  have hv : observed.2 ≤ canonicalProtocolOracleViewBudget equal read 11 initial.length produced.1.trace.length
      (protocolChallengeCount produced.1.trace) access replyRead :=
    canonicalProtocolOracleViewCosted_cost_le equal read initial produced.1.challenges
      (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace access replyRead hread hreply
  have hvFixed : observed.2 ≤ canonicalProtocolOracleViewBudget equal read 11 initial.length
      (72 * inputs.length + 107) 22 access replyRead := hv.trans (by
    rw [hcount]
    dsimp only [canonicalProtocolOracleViewBudget]
    gcongr)
  have ht := storedActionHonestTraceCosted_cost_le_fixed costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness bits
  change produced.2 + observed.2 + 3 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add ht hvFixed) 3

end Zcash.Snark.ZeroKnowledge
