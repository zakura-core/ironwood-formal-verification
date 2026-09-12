import Zcash.Snark.Fixtures.Prover.Commitment
import Zcash.Snark.Fixtures.Prover.Polynomial
import Zcash.Snark.ZeroKnowledge.IpaSampling

/-!
# Replaying all IPA messages

Each round caches its folded vectors before computing the next round. The existing
Vesta kernel supplies commitments and scalar multiplications. The resulting transcript
equals the reference IPA computation for every tape and supplied challenge sequence.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- Compute the round's two cross terms from the actual folded coefficient and generator vectors. -/
def crossTerms {k : ℕ} (z : Fp) (u : VestaG)
    (a b : Fin (2 ^ (k + 1)) → Fp) (g : Fin (2 ^ (k + 1)) → VestaG) : VestaG × VestaG :=
  (commitVector (loHalf g) (hiHalf a) + scale (z * innerProduct (hiHalf a) (loHalf b)) u,
    commitVector (hiHalf g) (loHalf a) + scale (z * innerProduct (loHalf a) (hiHalf b)) u)

/-- The two kernel commitments retain the reference cross-term equations. -/
theorem crossTerms_result {k : ℕ} (z : Fp) (u : VestaG)
    (a b : Fin (2 ^ (k + 1)) → Fp) (g : Fin (2 ^ (k + 1)) → VestaG) :
    crossTerms z u a b g = ipaCrossTerms z u a b g := by
  simp only [crossTerms, commitVector_result, scale_result, ipaCrossTerms]

/-- Cache each folded state once, retaining all earlier round messages. -/
def coreMessages (z : Fp) (u : VestaG) :
    (k : ℕ) → (Fin k → Fp) → (Fin (2 ^ k) → Fp) → (Fin (2 ^ k) → Fp) →
      (Fin (2 ^ k) → VestaG) → Vector (VestaG × VestaG) k
  | 0, _, _, _, _ => cacheFn Fin.elim0
  | k + 1, rounds, a, b, g =>
      let message := crossTerms z u a b g
      let rest := coreMessages z u k (fun j => rounds j.succ)
        (cacheFn (foldVec (loHalf a) (hiHalf a) (rounds 0)⁻¹)).get
        (cacheFn (loHalf b + rounds 0 • hiHalf b)).get
        (cacheFn (fun i => loHalf g i + scale (rounds 0) (hiHalf g i))).get
      cacheFn (Fin.cons message rest.get)

/-- Caching and kernel arithmetic preserve the complete recursive IPA message sequence. -/
theorem coreMessages_result (z : Fp) (u : VestaG) (k : ℕ) (rounds : Fin k → Fp)
    (a b : Fin (2 ^ k) → Fp) (g : Fin (2 ^ k) → VestaG) :
    (coreMessages z u k rounds a b g).get = ipaCoreMessages z u k rounds a b g := by
  induction k with
  | zero => exact cacheFn_result _
  | succ k ih =>
    simp only [coreMessages, cacheFn_result, scale_result, crossTerms_result, ih, ipaCoreMessages]
    rfl

/-- Build the mask commitment, every blinded round pair, and both final scalar responses. -/
def ipaTranscript {k : ℕ} (pub : IpaPublic k Fp VestaG)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) (alphas : Fin k → Fp)
    (blinds : IpaBlinds k Fp) : IpaTranscript k Fp VestaG :=
  let sparse := cacheFn (sparseIpaCoefficients pub.point alphas)
  let masked := cacheFn (coefficients + pub.xi • sparse.get - Pi.single 0 pub.value)
  let core := coreMessages pub.z pub.U k pub.rounds masked.get
    (cacheFn (evalVector k pub.point)).get (cacheFn pub.generators).get
  { maskCommitment := commitVector pub.generators sparse.get + scale blinds.1 pub.W
    messages := (cacheFn (fun j =>
      ((core.get j).1 + scale (blinds.2 j).1 pub.W, (core.get j).2 + scale (blinds.2 j).2 pub.W))).get
    scalar := foldByRounds k pub.rounds masked.get
    blind := ipaFinalBlind rho pub.xi pub.rounds blinds }

/-- The executable transcript is the reference honest IPA transcript on the same private coins. -/
theorem ipaTranscript_result {k : ℕ} (pub : IpaPublic k Fp VestaG)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) (alphas : Fin k → Fp)
    (blinds : IpaBlinds k Fp) :
    ipaTranscript pub coefficients rho alphas blinds =
      honestIpaTranscript pub coefficients rho alphas blinds := by
  simp only [ipaTranscript, cacheFn_result, commitVector_result, scale_result, coreMessages_result]
  rfl

/-- Decode the original ordered IPA tape; expected fixture messages are not inputs. -/
def ipaFromTape {k : ℕ} (pub : IpaPublic k Fp VestaG)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (tape : Fin (ipaSampleCount k) → Fp) : IpaTranscript k Fp VestaG :=
  let coins := ipaTapeEquiv k Fp tape
  ipaTranscript pub coefficients rho coins.1 coins.2

/-- Replay consumes precisely the tape used by the proved IPA sampling model. -/
theorem ipaFromTape_result {k : ℕ} (pub : IpaPublic k Fp VestaG)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) (tape : Fin (ipaSampleCount k) → Fp) :
    ipaFromTape pub coefficients rho tape = ipaTranscriptFromTape pub coefficients rho tape := by
  unfold ipaFromTape ipaTranscriptFromTape
  rw [ipaTranscript_result]

end Zcash.Snark.Fixtures.Prover
