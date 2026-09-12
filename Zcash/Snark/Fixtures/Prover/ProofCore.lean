import Zcash.Snark.Fixtures.Prover.Ipa
import Zcash.Snark.Fixtures.Prover.Opening
import Zcash.Snark.ZeroKnowledge.MultiopenIpa

/-!
# The computed multi-opening's IPA

The final IPA vector, inherited blind, and public value come from the computed
opening groups. These adapters use no expected transcript fields.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Store the requested coefficient prefix, padding missing coefficients with zero. -/
def padded (n : ℕ) (values : List Fp) : Vector Fp n :=
  let stored := values.toArray
  cacheFn (fun i => stored[i.val]?.getD 0)

/-- Stored prefix reads equal the reference polynomial's coefficient vector. -/
theorem padded_result (n : ℕ) (values : List Fp) :
    (padded n values).get = ZeroKnowledge.polynomialCoefficients n (densePolynomial values) := by
  funext i
  simp only [padded, cacheFn_result, List.getElem?_toArray, ZeroKnowledge.polynomialCoefficients,
    densePolynomial_coeff, List.getD_eq_getElem?_getD]

/-- Commit the same coefficient prefix and blind using the existing Vesta kernel. -/
def commitPolynomial {n : ℕ} (generators : Fin n → VestaG) (W : VestaG)
    (coefficients : List Fp) (blind : Fp) : VestaG :=
  commitVector generators (padded n coefficients).get + scale blind W

/-- The concrete commitment agrees with the model even when a coefficient list is short or long. -/
theorem commitPolynomial_result {n : ℕ} (generators : Fin n → VestaG) (W : VestaG)
    (coefficients : List Fp) (blind : Fp) :
    commitPolynomial generators W coefficients blind =
      polynomialCommitment generators W (densePolynomial coefficients) blind := by
  simp only [commitPolynomial, commitVector_result, padded_result, scale_result, polynomialCommitment]

/-- Compute the entire IPA from the actual opening polynomial and its inherited blinding. -/
def storedIpa (urs : URS VestaG) (data : StoredMultiopenData) (point xi z : Fp)
    (rounds : Fin urs.k → Fp) (tape : Fin (ipaSampleCount urs.k) → Fp) : IpaTranscript urs.k Fp VestaG :=
  let pub : IpaPublic urs.k Fp VestaG :=
    { generators := urs.g, W := urs.w, U := urs.u
      commitment := commitPolynomial urs.g urs.w data.coefficients data.blind
      point := point, value := data.value, xi := xi, z := z, rounds := rounds }
  ipaFromTape pub (padded (2 ^ urs.k) data.coefficients).get data.blind tape

/-- Stored multi-opening data supplies exactly the reference IPA's public and private inputs. -/
theorem storedIpa_result (urs : URS VestaG) (groups : List StoredOpeningGroup)
    (x2 x4 point quotientBlind xi z : Fp) (rounds : Fin urs.k → Fp)
    (tape : Fin (ipaSampleCount urs.k) → Fp)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 4) :
    storedIpa urs (openingData groups x2 x4 point quotientBlind) point xi z rounds tape =
      ipaTranscriptFromTape
        (computedMultiopenIpaPublic urs x2 x4 point xi z quotientBlind rounds
          (groups.map StoredOpeningGroup.erase))
        (ZeroKnowledge.polynomialCoefficients (2 ^ urs.k)
          (multiopenFinalPolynomial x2 x4 (groups.map StoredOpeningGroup.erase)))
        (multiopenFinalBlind x4 quotientBlind (groups.map StoredOpeningGroup.erase)) tape := by
  simp only [storedIpa, ipaFromTape_result, padded_result, commitPolynomial_result, openingData]
  rw [storedMultiopenDataCosted_polynomial_result _ _ _ _ _ _ _ _ _ hpoints,
    storedMultiopenDataCosted_blind_result,
    storedMultiopenDataCosted_value_result _ _ _ _ _ _ _ _ _ hpoints]
  simp only [computedMultiopenIpaPublic, IpaPublic.ofMsm, computedMultiopenOpening_commitment]

end Zcash.Snark.Fixtures.Prover
