import Zcash.Snark.ZeroKnowledge.TranscriptArgumentBlocksCost

/-!
# Complete producer bounds for the verifier's proof fields

A price attached to a field includes its whole producer, including routing and
any arithmetic needed to obtain it. These are bounds on every field that the
actual message schedule may read, rather than a cost for storing a closure.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Erase only the prices, preserving every original proof field and optional claim. -/
def eraseProofCosts {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) : ProofString shape F G where
  adviceCommitments := fun action column => (proof.adviceCommitments action column).1
  lookupPermutedInput := fun action lookup => (proof.lookupPermutedInput action lookup).1
  lookupPermutedTable := fun action lookup => (proof.lookupPermutedTable action lookup).1
  permutationProduct := fun action set => (proof.permutationProduct action set).1
  lookupProduct := fun action lookup => (proof.lookupProduct action lookup).1
  vanishingRandom := proof.vanishingRandom.1
  hPieces := fun piece => (proof.hPieces piece).1
  instanceEvals := fun action query => (proof.instanceEvals action query).1
  adviceEvals := fun action query => (proof.adviceEvals action query).1
  fixedEvals := fun query => (proof.fixedEvals query).1
  vanishingRandomEval := proof.vanishingRandomEval.1
  permutationCommonEvals := fun column => (proof.permutationCommonEvals column).1
  permutationSetEvals := fun action set => (proof.permutationSetEvals action set).map Prod.fst
  lookupEvals := fun action lookup => (proof.lookupEvals action lookup).map Prod.fst
  multiopenQPrime := proof.multiopenQPrime.1
  multiopenU := fun group => (proof.multiopenU group).1
  ipaS := proof.ipaS.1
  ipaRounds := fun round => ((proof.ipaRounds round).1.1, (proof.ipaRounds round).2.1)
  ipaC := proof.ipaC.1
  ipaF := proof.ipaF.1

/-- A common envelope for every complete point and scalar producer in the proof. -/
structure ProofFieldReadBound {shape : Shape} {F G : Type*}
    (proof : ProofString shape (F × ℕ) (G × ℕ)) (access : ℕ) : Prop where
  adviceCommitments : ∀ action column, (proof.adviceCommitments action column).2 ≤ access
  lookupPermutedInput : ∀ action lookup, (proof.lookupPermutedInput action lookup).2 ≤ access
  lookupPermutedTable : ∀ action lookup, (proof.lookupPermutedTable action lookup).2 ≤ access
  permutationProduct : ∀ action set, (proof.permutationProduct action set).2 ≤ access
  lookupProduct : ∀ action lookup, (proof.lookupProduct action lookup).2 ≤ access
  vanishingRandom : proof.vanishingRandom.2 ≤ access
  hPieces : ∀ piece, (proof.hPieces piece).2 ≤ access
  instanceEvals : ∀ action query, (proof.instanceEvals action query).2 ≤ access
  adviceEvals : ∀ action query, (proof.adviceEvals action query).2 ≤ access
  fixedEvals : ∀ query, (proof.fixedEvals query).2 ≤ access
  vanishingRandomEval : proof.vanishingRandomEval.2 ≤ access
  permutationCommonEvals : ∀ column, (proof.permutationCommonEvals column).2 ≤ access
  permutationSetEvals : ∀ action set, permSetReadBound (proof.permutationSetEvals action set) access
  lookupEvals : ∀ action lookup, lookupEvalReadBound (proof.lookupEvals action lookup) access
  multiopenQPrime : proof.multiopenQPrime.2 ≤ access
  multiopenU : ∀ group, (proof.multiopenU group).2 ≤ access
  ipaS : proof.ipaS.2 ≤ access
  ipaRounds : ∀ round, (proof.ipaRounds round).1.2 ≤ access ∧ (proof.ipaRounds round).2.2 ≤ access
  ipaC : proof.ipaC.2 ≤ access
  ipaF : proof.ipaF.2 ≤ access

end Zcash.Snark.ZeroKnowledge
