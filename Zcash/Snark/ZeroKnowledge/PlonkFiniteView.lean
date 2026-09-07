import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Mathlib.Tactic.DeriveFintype

/-!
# The finite raw space of one complete attempt

Every coordinate is a field or group element, with vector lengths fixed by the
public shape. These instances are for probability proofs. The field-coin prover
and simulator do not enumerate this space, and encoded histories remain lists.
-/

namespace Zcash.Snark.ZeroKnowledge

instance plonkFinitePermSetEval {F : Type*} [Fintype F] : Fintype (PermSetEval F) :=
  derive_fintype% _

instance plonkFiniteLookupEval {F : Type*} [Fintype F] : Fintype (LookupEval F) :=
  derive_fintype% _

-- The twenty coordinates produce a larger instance term than the default search-size limit.
set_option synthInstance.maxSize 256 in
noncomputable instance plonkFiniteProofString {shape : Shape} {F G : Type*} [Fintype F] [Fintype G] :
    Fintype (ProofString shape F G) := by
  classical
  let pack (p : ProofString shape F G) :=
    (p.adviceCommitments, p.lookupPermutedInput, p.lookupPermutedTable, p.permutationProduct,
     p.lookupProduct, p.vanishingRandom, p.hPieces, p.instanceEvals, p.adviceEvals, p.fixedEvals,
     p.vanishingRandomEval, p.permutationCommonEvals, p.permutationSetEvals, p.lookupEvals,
     p.multiopenQPrime, p.multiopenU, p.ipaS, p.ipaRounds, p.ipaC, p.ipaF)
  apply Fintype.ofInjective pack
  intro a b h
  cases a
  cases b
  simpa only [pack, Prod.mk.injEq, ProofString.mk.injEq] using h

noncomputable instance plonkFiniteChallenges {k : ℕ} {F : Type*} [Fintype F] :
    Fintype (Challenges k F) := by
  classical
  let pack (ch : Challenges k F) :=
    (ch.theta, ch.beta, ch.gamma, ch.y, ch.x, ch.x1, ch.x2, ch.x3, ch.x4, ch.xi, ch.z, ch.ipaRound)
  apply Fintype.ofInjective pack
  intro a b h
  cases a
  cases b
  simpa only [pack, Prod.mk.injEq, Challenges.mk.injEq] using h

end Zcash.Snark.ZeroKnowledge
