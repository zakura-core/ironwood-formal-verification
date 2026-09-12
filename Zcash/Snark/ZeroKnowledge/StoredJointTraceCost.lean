import Zcash.Snark.ZeroKnowledge.StoredJointProofBound
import Zcash.Snark.ZeroKnowledge.TranscriptScheduleBound

/-! # Complete stored-joint to original-transcript runtime composition -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Prepare the original proof and force every transcript field, retaining both complete costs. -/
def storedJointTraceCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) :
    List (TranscriptElt Fp G) × ℕ :=
  let proof := storedJointProofCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint
  let trace := plonkAttemptTraceCosted proof.1
  (trace.1, proof.2 + trace.2 + 3)

/-- The complete stored constructor emits exactly the original joint view's full schedule. -/
theorem storedJointTraceCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    (storedJointTraceCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1
      (materializePlonkJointView view)).1 =
      plonkAttemptTrace (plonkProofFromJointView
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 x1.1 view) := by
  simp only [storedJointTraceCosted, plonkAttemptTraceCosted_result, storedJointProofCosted_result]

/-- Full preparation and schedule construction share one explicit stored-data bound. -/
theorem storedJointTraceCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G)
    (rowRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hrows : ∀ row ∈ joint.1.2.1, row.length ≤ 5) :
    let access := routedProofReadBudget actions joint.1.2.1.length equal read
      (storedJointProofInputBudget costs read omegaAccess rowRead x.2 joint.1.1.length joint.2.messages.length)
    let preparation := 3 * joint.1.2.1.length + read +
      4 * (privateOpeningEvaluationCostBudget costs equal read actions joint.1.2.1.length (read + 11) x1.2 + 1) + 65
    (storedJointTraceCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).2 ≤
      preparation + 8 * actions * actions + (72 * actions + 2 * k + 63) * access +
        1300 * actions + k * k + 15 * k + 1903 := by
  have hp := storedJointProofCosted_cost_le (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint hrows
  have hr := storedJointProofCosted_readBound (k := k) costs equal read omegaAccess
    instances fixed sigma x x1 joint rowRead hinstances hfixed hsigma hrows
  have ht := plonkAttemptTraceCosted_cost_le
    (storedJointProofCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).1 _ hr
  dsimp only [storedJointTraceCosted]
  omega

end Zcash.Snark.ZeroKnowledge
