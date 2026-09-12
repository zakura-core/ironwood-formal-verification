import Zcash.Snark.ZeroKnowledge.StoredMultiopenDataBound
import Zcash.Snark.ZeroKnowledge.DenseCommitmentCost
import Zcash.Snark.ZeroKnowledge.HonestIpaTapeCost
import Zcash.Snark.ZeroKnowledge.IpaPreparedInputCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Prepare the actual polynomial commitment and claimed value before running the complete real IPA. -/
@[irreducible] def preparedHonestIpaCosted (costs : FieldOperationCosts) (groupAdd groupScale equal read : ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ) (data : StoredMultiopenData × ℕ)
    (q xi z : Fp × ℕ) (rounds : Fin 11 → Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    MaterializedIpaTranscript Fp G × ℕ :=
  let commitment := densePolynomialCommitmentCosted read groupAdd groupScale generators W
    (data.1.coefficients, read + 1) (data.1.blind, read + 1)
  let input := prepareIpaPublicCosted generators W U
    ((commitment.1, data.1.value), commitment.2 + read + 1) q xi z rounds
  let result := honestIpaTranscriptFromTapeCosted costs groupAdd groupScale equal input.1
    (fun i => getDListCosted read (0 : Fp) data.1.coefficients i.val) (data.1.blind, read + 1) tape
  (result.1, data.2 + input.2 + result.2 + 1)

/-- Erasure identifies the complete original IPA on the stored polynomial, blind, and supplied claimed value. -/
theorem preparedHonestIpaCosted_result (costs : FieldOperationCosts) (groupAdd groupScale equal read : ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ) (data : StoredMultiopenData × ℕ)
    (q xi z : Fp × ℕ) (rounds : Fin 11 → Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ) :
    (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data q xi z rounds tape).1 =
      materializedIpaTranscript (ipaTranscriptFromTape
        ({ generators := fun i => (generators i).1
           W := W.1
           U := U.1
           commitment := polynomialCommitment (fun i => (generators i).1) W.1
             (densePolynomial data.1.coefficients) data.1.blind
           point := q.1
           value := data.1.value
           xi := xi.1
           z := z.1
           rounds := fun i => (rounds i).1 } : IpaPublic 11 Fp G)
        (Zcash.Snark.ZeroKnowledge.polynomialCoefficients 2048 (densePolynomial data.1.coefficients))
        data.1.blind (fun i => (tape i).1)) := by
  have hc : Zcash.Snark.ZeroKnowledge.polynomialCoefficients 2048 (densePolynomial data.1.coefficients) =
      (fun i : Fin 2048 => data.1.coefficients.getD i.val 0) := by
    funext i
    exact densePolynomial_coeff data.1.coefficients i.val
  unfold preparedHonestIpaCosted
  change (honestIpaTranscriptFromTapeCosted costs groupAdd groupScale equal
    (prepareIpaPublicCosted generators W U
      (((densePolynomialCommitmentCosted read groupAdd groupScale generators W
        (data.1.coefficients, read + 1) (data.1.blind, read + 1)).1, data.1.value),
        (densePolynomialCommitmentCosted read groupAdd groupScale generators W
          (data.1.coefficients, read + 1) (data.1.blind, read + 1)).2 + read + 1) q xi z rounds).1
    (fun i => getDListCosted read (0 : Fp) data.1.coefficients i.val) (data.1.blind, read + 1) tape).1 = _
  rewrite [honestIpaTranscriptFromTapeCosted_result, prepareIpaPublicCosted_result, densePolynomialCommitmentCosted_result]
  rewrite [hc]
  simp only [getDListCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
