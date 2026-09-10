import Zcash.Snark.ZeroKnowledge.PlonkQuotientSimulation
import Zcash.Snark.ZeroKnowledge.PlonkDegree

/-!
# Joint simulation with the quotient capacity derived

The circuit's public degree profile proves capacity for every reachable private row
state. Constraint divisibility is this theorem's private-state premise. The public
polynomial, generator, and supplied-challenge conditions remain explicit. The result
compares the algebraic proof views supplied by PlonkQuotientSimulation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common
open CompPoly

/-- The complete algebraic proof law, deriving quotient capacity from public circuit syntax. -/
theorem sampledPlonkVerifier_capacity_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hdiv : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub ch rows)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : ch.xi ≠ 0)
    (hu : ∀ j, ch.ipaRound j ≠ 0) (hx : ch.x ^ 2048 ≠ 1)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) ch.x ch.x3))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048,
      plonkObservationPoints (omegaOf 11) ch.x ch.x3 i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkVerifierProver construct history urs vk pub ch)
        (idealPlonkVerifierSimulator urs vk pub ch) ((fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkVerifierSimulator urs vk pub ch)
        (sampledPlonkVerifierProver construct history urs vk pub ch)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) := by
  exact sampledPlonkVerifier_simulation_error_bound construct history urs hk vk pub ch
    homega hn hblind hinstance hfixed hsigma
    (fun rows _ => plonkConstraintNumerator_natDegree_lt vk pub ch rows profile hinstance hfixed hsigma)
    hdiv hW hxi hu hx hpoints haway

end Zcash.Snark.ZeroKnowledge
