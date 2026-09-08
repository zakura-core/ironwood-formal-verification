import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedSource
import Zcash.Snark.ZeroKnowledge.GeneratedRetryStreamTail
import Zcash.Snark.ZeroKnowledge.PrngSecurity

/-!
# Complete Action retry histories from a fresh private seed

One fresh uniform bit seed initializes the continuing private generator. Oracle
reply slots come from an independent infinite uniform tape. The observed stream
retains every attempt and public cache, including possible nontermination, while
erasing every private generator state. No PRNG security is needed to define this
normalized law or to prove its exact finite projections.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open MeasureTheory Zcash.Common
open scoped ENNReal

/-- The complete Action oracle history from one fresh seed and an independent public reply stream. -/
noncomputable def actionGeneratedOracleRetryStream {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) (cache : ActionRetryOracleState) :
    Measure (ℕ → ActionRetryStreamEntry) :=
  seededGeneratedRetryStreamLaw (fun state coins tape =>
    actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape))
    oracleRetrySet (drawGeneratorTape next (fieldSampleCount actions))
    (uniformSeedTapeSource seedBits initState) cache

/-- The complete seeded Action experiment has total mass one without a termination premise. -/
instance actionGeneratedOracleRetryStream_isProbabilityMeasure {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) (cache : ActionRetryOracleState) :
    IsProbabilityMeasure (actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr
      next seedBits initState cache) := by
  unfold actionGeneratedOracleRetryStream
  infer_instance

/-- Clipping the seeded stream is exactly replay from the generated private prefix covered by the PRNG game. -/
theorem actionGeneratedOracleRetryStream_truncate {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState) :
    (actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache).map
        (truncateRetryStream budget) =
      ((actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
        (uniformSeedTapeSource seedBits (fun seed => actionGeneratorRetryTape next actions budget (initState seed)))
        cache).map (fun output index => output.1.attempts[index]?)).toMeasure := by
  rw [actionGeneratedOracleRetryStream, seededGeneratedRetryStreamLaw_truncate,
    actionOracleRecordFromSource_generated]
  simp only [uniformSeedTapeSource, seededTapeSource, PMF.map_comp, Function.comp_def]

/-- Truncation charges actual generated-prefix exhaustion, with no per-seed stopping or independence assumption. -/
theorem actionGeneratedOracleRetryStream_truncation_error_bound {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ) (cache : ActionRetryOracleState) :
    let law := actionGeneratedOracleRetryStream urs hk inputs witness vkTranscriptRepr next seedBits initState cache
    let error := (actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
      (uniformSeedTapeSource seedBits (fun seed => actionGeneratorRetryTape next actions budget (initState seed)))
      cache).toOuterMeasure {output | output.1.exhausted = true}
    MeasureEventBiasLE law (law.map (truncateRetryStream budget)) error ∧
      MeasureEventBiasLE (law.map (truncateRetryStream budget)) law error := by
  have h := seededGeneratedRetryStreamLaw_truncation_error_bound
    (fun state coins tape => actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape))
    oracleRetrySet (drawGeneratorTape next (fieldSampleCount actions))
    (uniformSeedTapeSource seedBits initState) budget cache
  rw [actionOracleRecordFromSource_generated] at h
  simpa only [actionGeneratedOracleRetryStream, uniformSeedTapeSource, seededTapeSource,
    PMF.map_comp, Function.comp_def] using h

end Zcash.Snark.ZeroKnowledge
