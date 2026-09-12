import Zcash.Snark.ZeroKnowledge.ActionOracleModel
import Zcash.Snark.ZeroKnowledge.ProtocolCacheCost

/-!
# Cache-phase bound for the Action protocol

The actual initial transcript contains the verifying-key representative and one
instance commitment per Action. At eleven IPA rounds, programming a materialized
attempt view costs at most `22 ((q + 22) (9490m + 14207) + 4) + 2` structural units.
Here `q` is the number of initially cached entries, and `m` is the Action count.
This bounds the byte-cache phase only; producing the view is not charged here.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action

/-- Count the actual public initialization, independently of commitment values. -/
theorem actionOracleInitial_length {actions : ℕ} (urs : URS VestaG) (vkTranscriptRepr : Fp)
    (inputs : Fin actions → PublicInputs Fp) :
    (actionOracleInitial urs vkTranscriptRepr inputs).length = actions + 1 := by
  simp only [actionOracleInitial, initialTranscript_length, plonkProofShape, FixtureMax.shape,
    Nat.mul_one, Nat.add_comm]

/-- The complete Action schedule has a public linear byte envelope, including exceptional cases. -/
theorem actionQueryAddress_bytes_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (proof : ProofString (plonkProofShape actions urs.k) Fp VestaG) (index : ℕ) :
    (protocolQueryAddress (actionOracleInitial urs vkTranscriptRepr inputs)
      (plonkAttemptTrace proof) index).1.length +
      (protocolQueryAddress (actionOracleInitial urs vkTranscriptRepr inputs)
        (plonkAttemptTrace proof) index).2.length ≤ 4745 * actions + 7101 := by
  have h := plonkQueryAddress_bytes_le (actionOracleInitial urs vkTranscriptRepr inputs) proof index
  apply h.trans
  rw [actionOracleInitial_length, hk]
  omega

/-- Count cache programming for any actual Action view, retaining all early-collision work. -/
theorem actionOracleView_programming_cost_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions urs.k) Fp VestaG) :
    (programOracleViewCosted cache
      (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) digests proof)).2 ≤
      22 * ((cache.length + 22) * (9490 * actions + 14207) + 4) + 2 := by
  have h := plonkRawOracleView_programming_cost_le cache
    (actionOracleInitial urs vkTranscriptRepr inputs) digests proof
  apply h.trans_eq
  rw [actionOracleInitial_length, hk]
  ring

end Zcash.Snark.ZeroKnowledge
