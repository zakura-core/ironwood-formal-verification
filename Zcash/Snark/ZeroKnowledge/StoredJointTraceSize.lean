import Zcash.Snark.ZeroKnowledge.StoredJointTraceCost
import Zcash.Snark.ZeroKnowledge.TranscriptScheduleSize

/-! # Exact challenge count and linear size of every stored-joint transcript -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- The stored constructor retains the original linear schedule size at every stored input. -/
theorem storedJointTraceCosted_length_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) :
    (storedJointTraceCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).1.length ≤
      72 * actions + 3 * k + 74 :=
  plonkAttemptTraceCosted_length_le
    (storedJointProofCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).1

/-- All original receive markers are present before the later observer applies its stopping policy. -/
theorem storedJointTraceCosted_challengeCount (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) :
    protocolChallengeCount
      (storedJointTraceCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).1 = k + 11 := by
  change protocolChallengeCount
    (plonkAttemptTraceCosted
      (storedJointProofCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).1).1 = _
  rw [plonkAttemptTraceCosted_result, plonkAttemptTrace_challengeCount]
  omega

end Zcash.Snark.ZeroKnowledge
