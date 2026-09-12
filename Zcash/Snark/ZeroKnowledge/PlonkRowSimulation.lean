import Zcash.Snark.ZeroKnowledge.PlonkCapacitySimulation
import Zcash.Snark.ZeroKnowledge.DomainDivisibility

/-!
# Joint simulation from row-wise constraint satisfaction

The supplied honest row construction must satisfy each gate, permutation, and lookup
constraint on every domain row. This endpoint derives exact quotient division and the
eight-piece capacity before applying the full-tape simulation theorem. It retains the
public degree profile and good supplied challenges. Correctness of the actual lookup
sorting and product recurrences, and the complete failure law, are still separate work.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common

/-- Full algebraic proof simulation with its quotient premises derived from row correctness. -/
theorem sampledPlonkVerifier_rows_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hrows : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      ∀ poly ∈ (plonkConstraintModel vk pub ch rows).constraints,
        ∀ i : Fin 2048, poly.eval (omegaOf 11 ^ i.val) = 0)
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
  exact sampledPlonkVerifier_capacity_simulation_error_bound construct history urs hk vk pub ch
    profile homega hn hblind hinstance hfixed hsigma
    (fun rows hsupport => plonkConstraintNumerator_dvd_of_rows vk pub ch rows (hrows rows hsupport))
    hW hxi hu hx hpoints haway

end Zcash.Snark.ZeroKnowledge
