import Zcash.Snark.ZeroKnowledge.IpaCoreMessagesBound
import Zcash.Snark.ZeroKnowledge.IpaWitnessInputsBound
import Zcash.Snark.ZeroKnowledge.IpaFinalBlindCost
import Zcash.Snark.ZeroKnowledge.VectorCommitmentCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Read and blind both actual real-prover cross terms, retaining the complete core computation. -/
def honestIpaRoundCosted (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) (index : Fin k) :
    (G × ℕ) × (G × ℕ) :=
  let core := ipaCoreMessagesCosted costs groupAdd groupScale pub.z pub.U k pub.rounds
    (ipaMaskedVectorCosted costs equal pub coefficients alphas)
    (ipaEvaluationReaderCosted costs.multiply pub.point) pub.generators index
  let blind := blinds index
  ((core.1.1 + blind.1.1 • pub.W.1, core.2 + blind.2 + pub.W.2 + groupAdd + groupScale + 1),
    (core.1.2 + blind.1.2 • pub.W.1, core.2 + blind.2 + pub.W.2 + groupAdd + groupScale + 1))

/-- Both counted points are exactly the original independently blinded cross terms. -/
theorem honestIpaRoundCosted_result (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (alphas : Fin k → F × ℕ) (blinds : Fin k → (F × F) × ℕ) (index : Fin k) :
    ((honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds index).1.1,
      (honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds index).2.1) =
      blindIpaMessages pub.W.1
        (ipaCoreMessages pub.z.1 pub.U.1 k (fun i => (pub.rounds i).1)
          (ipaMaskedVector pub.erase (fun i => (coefficients i).1) (fun i => (alphas i).1))
          (evalVector k pub.point.1) (fun i => (pub.generators i).1))
        (fun i => (blinds i).1) index := by
  simp only [honestIpaRoundCosted, ipaCoreMessagesCosted_result, ipaMaskedVectorCosted_result,
    ipaEvaluationReaderCosted_result, blindIpaMessages]

/-- Count all fields of the actual IPA prover; materialization below forces every round. -/
def honestIpaTranscriptCosted (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (alphas : Fin k → F × ℕ) (mask : F × ℕ)
    (blinds : Fin k → (F × F) × ℕ) : IpaTranscript k (F × ℕ) (G × ℕ) where
  maskCommitment :=
    let commitment := vectorCommitmentCosted groupAdd groupScale pub.generators
      (sparseIpaCoefficientCosted costs equal pub.point alphas)
    (commitment.1 + mask.1 • pub.W.1, commitment.2 + mask.2 + pub.W.2 + groupAdd + groupScale + 1)
  messages := honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds
  scalar := ipaWitnessScalarCosted costs k pub.rounds (ipaMaskedVectorCosted costs equal pub coefficients alphas)
  blind := ipaFinalBlindCosted costs rho pub.xi mask pub.rounds blinds

/-- All erased fields agree jointly with the original honest transcript for every input. -/
theorem honestIpaTranscriptCosted_result (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (alphas : Fin k → F × ℕ) (mask : F × ℕ)
    (blinds : Fin k → (F × F) × ℕ) :
    (honestIpaTranscriptCosted costs groupAdd groupScale equal pub coefficients rho alphas mask blinds).eraseCosts =
      honestIpaTranscript pub.erase (fun i => (coefficients i).1) rho.1 (fun i => (alphas i).1)
        (mask.1, fun i => (blinds i).1) := by
  have hm : (fun i =>
      ((honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds i).1.1,
        (honestIpaRoundCosted costs groupAdd groupScale equal pub coefficients alphas blinds i).2.1)) =
      blindIpaMessages pub.W.1
        (ipaCoreMessages pub.z.1 pub.U.1 k (fun i => (pub.rounds i).1)
          (ipaMaskedVector pub.erase (fun i => (coefficients i).1) (fun i => (alphas i).1))
          (evalVector k pub.point.1) (fun i => (pub.generators i).1)) (fun i => (blinds i).1) := by
    funext i
    exact honestIpaRoundCosted_result costs groupAdd groupScale equal pub coefficients alphas blinds i
  simp only [honestIpaTranscriptCosted, IpaTranscript.eraseCosts, vectorCommitmentCosted_result,
    sparseIpaCoefficientCosted_result, ipaWitnessScalarCosted_result, ipaMaskedVectorCosted_result,
    ipaFinalBlindCosted_result, hm, honestIpaTranscript, maskedIpaScalar, ipaMaskedVector, IpaPublicCosted.erase]

/-- Fully materialized cost erasure preserves the complete original IPA observation. -/
theorem materializedHonestIpaCosted_result (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (alphas : Fin k → F × ℕ) (mask : F × ℕ)
    (blinds : Fin k → (F × F) × ℕ) :
    (materializeIpaCosted (honestIpaTranscriptCosted costs groupAdd groupScale equal
      pub coefficients rho alphas mask blinds)).1 =
      materializedIpaTranscript (honestIpaTranscript pub.erase (fun i => (coefficients i).1) rho.1
        (fun i => (alphas i).1) (mask.1, fun i => (blinds i).1)) := by
  rewrite [materializeIpaCosted_result, honestIpaTranscriptCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
