import Zcash.Snark.ZeroKnowledge.ActionGeneratorStreamPrng
import Zcash.Snark.ZeroKnowledge.RetryStreamNontermination

/-!
# The seeded Action run's nontermination bound

Only the finite exhaustion detector needs to belong to the PRNG test class.
The complete law itself is defined independently of termination. This result
does not infer zero nontermination mass or independent generated attempt blocks.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open MeasureTheory Zcash.Common
open scoped ENNReal

/-- The admitted exhaustion reduction also bounds the complete seeded run's nontermination event. -/
theorem actionGeneratedOracleRetryStream_nontermination_le [Fintype VestaG] {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (next : Generator → Fin challengeDigestCard × Generator)
    (seedBits : ℕ) (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState)
    (admissible : Set (Unit → RawPrivateRetryTape actions budget → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits
      (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) (PMF.pure ()) admissible η)
    (htail : actionOracleRecordPrngReduction urs hk inputs witness vkTranscriptRepr budget cache
      (fun output => output.1.exhausted) ∈ admissible) :
    (actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache)
        retryStreamNontermination ≤
      actionOracleRetryRate actions ^ budget + oracleRetryPotential actions cache.length + η := by
  have ht := actionOracleRecordPrng_exhaustion_le urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache seedBits
    (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) admissible η secure htail
  have h := (actionGeneratedOracleRetryStream_truncation_error_bound urs hk inputs witness vkTranscriptRepr
    next seedBits initState budget cache).1
  have hb := (h.mono ht) retryStreamNontermination retryStreamNontermination_measurable
  simpa only [truncateRetryStream_nontermination_measure_zero, zero_add] using hb

/-- The numerical retry certificate gives a simple binary exhaustion contribution. -/
theorem actionOracleRetryRate_pow_le_half [Fintype VestaG] {actions : ℕ}
    (hpositive : 1 ≤ actions) (hsize : actions ≤ 65535) (budget : ℕ) :
    actionOracleRetryRate actions ^ budget ≤ (1 / 2 : ℝ≥0∞) ^ budget :=
  pow_le_pow_left' (actionOracleRetryRate_lt_half hpositive hsize).le budget

end Zcash.Snark.ZeroKnowledge
