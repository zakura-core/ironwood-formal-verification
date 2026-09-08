import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedSource
import Zcash.Snark.ZeroKnowledge.PrngSecurity

/-!
# PRNG tests of complete finite Action observations

The reduction receives one whole candidate private prefix and supplies independent
raw oracle reply slots. Its observation includes every intermediate public cache.
The same security game applies to a view test and to the explicit exhaustion bit;
membership of both complete reductions in the admissible class is a premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- Test the complete recorded reference execution from one whole candidate private prefix. -/
noncomputable def actionOracleRecordPrngReduction {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (cache : ActionRetryOracleState) (test : ActionRetryRecordedView → Bool) :
    Unit → RawPrivateRetryTape actions budget → PMF Bool :=
  fun _ => tapeReduction (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget))
    (fun replies tape => actionOracleRecordFromRawTapes urs hk inputs witness vkTranscriptRepr replies tape cache)
    (fun output => PMF.pure (test output))

/-- Testing the actual finite source law is exactly the displayed whole-prefix PRNG reduction. -/
theorem actionOracleRecordPrngReduction_law {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (cache : ActionRetryOracleState) (source : PMF (RawPrivateRetryTape actions budget))
    (test : ActionRetryRecordedView → Bool) :
    (actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr source cache).map test =
      auxiliaryPrngGame (PMF.pure ()) source
        (actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache test) := by
  change (sourceTapeExperiment (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget)) source
      (fun replies tape => actionOracleRecordFromRawTapes urs hk inputs witness vkTranscriptRepr replies tape cache)).bind
      (fun output => PMF.pure (test output)) = _
  rw [tapeReduction_law, auxiliaryPrngGame, PMF.pure_bind]
  rfl

/-- An admitted recorded-view test has exactly the assumed whole-prefix distinguishing bound. -/
theorem actionOracleRecordPrng_test_error_bound {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (cache : ActionRetryOracleState) (seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateRetryTape actions budget)
    (test : ActionRetryRecordedView → Bool)
    (admissible : Set (Unit → RawPrivateRetryTape actions budget → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (PMF.pure ()) admissible η)
    (hclass : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache test ∈ admissible) :
    PMFEventBiasLE
        ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr (uniformSeedTapeSource seedBits generate) cache).map test)
        ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache).map test) η ∧
      PMFEventBiasLE
        ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache).map test)
        ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr (uniformSeedTapeSource seedBits generate) cache).map test) η := by
  simp only [actionOracleRecordPrngReduction_law]
  exact uniformSeedPrngSecure_event_bias secure hclass

/-- The admitted finite exhaustion test bounds the actual generated continuation tail. -/
theorem actionOracleRecordPrng_exhaustion_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) (seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateRetryTape actions budget)
    (admissible : Set (Unit → RawPrivateRetryTape actions budget → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (PMF.pure ()) admissible η)
    (hclass : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => output.1.exhausted) ∈ admissible) :
    (actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr (uniformSeedTapeSource seedBits generate) cache).toOuterMeasure
        {output | output.1.exhausted = true} ≤
      actionOracleRetryRate actions ^ budget + oracleRetryPotential actions cache.length + η := by
  have h := (actionOracleRecordPrng_test_error_bound urs hk inputs witness vkTranscriptRepr budget cache
    seedBits generate (fun output => output.1.exhausted) admissible η secure hclass).1 {true}
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage, Set.mem_singleton_iff] at h
  exact h.trans (add_le_add
    (actionOracleRecordFromSource_exhaustion_le urs hk inputs witness hvalid hpositive hW hhalf vkTranscriptRepr budget cache) le_rfl)

end Zcash.Snark.ZeroKnowledge
