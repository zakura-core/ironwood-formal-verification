import Zcash.Snark.Fixtures.Prover.Material
import Zcash.Snark.Fixtures.Prover.RowsProof
import Zcash.Snark.ZeroKnowledge.PlonkCausality

/-!
# Complete fixed-tape prover execution

This computation starts with the synthesized witness and public rows, the received
challenges, and the complete private tape. The theorem identifies its result with
the reference prover used by the zero-knowledge development for every such input.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Split the complete tape after the last pre-IPA sample, preserving every index. -/
def executionTapes {actions : ℕ} (tape : Fin (fieldSampleCount actions) → Fp) :
    (Fin (148 * actions + 12) → Fp) × (Fin (ipaSampleCount 11) → Fp) :=
  splitTapeEquiv (148 * actions + 12) (ipaSampleCount 11) Fp
    (fun i => tape ⟨i.val, by
      have h := i.isLt
      simp only [fieldSampleCount, ipaSampleCount] at *
      omega⟩)

/-- The fixed-size split selects the identical indices as the reference batch-dependent split. -/
theorem executionTapes_result {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (fieldSampleCount actions) → Fp) :
    splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12) (ipaSampleCount 11) Fp
      (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl)) =
        (materialTape construct (executionTapes tape).1, (executionTapes tape).2) := by
  apply Prod.ext
  · funext i
    rfl
  · funext i
    change tape _ = tape _
    congr 1
    apply Fin.ext
    change batchedColumnSampleCount (plonkColumnBatches construct) + 12 + i.val =
      148 * actions + 12 + i.val
    rw [plonkColumnBatches_sample_count]

/-- The original joint view after private material has been constructed. -/
def referenceFinish {actions : ℕ} (urs : URS VestaG)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (ch : Challenges urs.k Fp)
    (prepared : PlonkPrivateMaterial actions) (tape : Fin (ipaSampleCount urs.k) → Fp) :
    ProofString (plonkProofShape actions urs.k) Fp VestaG :=
  let pieces := plonkHonestQuotientPieces vk pub ch
  let data := plonkIpaData urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound pieces prepared
  plonkProofFromJointView pub ch.x ch.x1
    (plonkMaskViewFromMaterial urs pub ch.x ch.x1 ch.x2 ch.x3 pieces prepared,
      ipaTranscriptFromTape data.1 data.2.1 data.2.2 tape)

/-- Compute the quotient and all remaining proof fields from the stored private material. -/
def finish {actions : ℕ} (urs : URS VestaG)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (ch : Challenges urs.k Fp)
    (prepared : PlonkPrivateMaterial actions) (tape : Fin (ipaSampleCount urs.k) → Fp) :
    ProofString (plonkProofShape actions urs.k) Fp VestaG :=
  let pieces := quotientPieces vk pub ch (columnCoefficients prepared.1)
  proofFromRows urs pub ch prepared.1 pieces prepared.2.1 prepared.2.2 tape

/-- The executable quotient and message assembly equal the original material observer. -/
theorem finish_result {actions : ℕ} (urs : URS VestaG)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (ch : Challenges urs.k Fp)
    (prepared : PlonkPrivateMaterial actions) (tape : Fin (ipaSampleCount urs.k) → Fp) :
    finish urs vk pub ch prepared tape = referenceFinish urs vk pub ch prepared tape := by
  have hp (j : Fin 8) :
      densePolynomial ((quotientPieces vk pub ch (columnCoefficients prepared.1)).getD j.val []) =
        plonkHonestQuotientPieces vk pub ch prepared.1 j := by
    rw [polynomial_getD, quotientPieces_result, List.getD_eq_getElem _ 0 (by simp)]
    simp only [List.getElem_ofFn, plonkHonestQuotientPieces]
  have hc : plonkCommitmentCores urs pub ch.x ch.x1 ch.x2
      (fun _ => plonkHonestQuotientPieces vk pub ch prepared.1) prepared.1 prepared.2.1 =
      plonkCommitmentCores urs pub ch.x ch.x1 ch.x2 (plonkHonestQuotientPieces vk pub ch)
        prepared.1 prepared.2.1 := by
    unfold plonkCommitmentCores plonkCommitmentPolynomials
    rfl
  simp only [finish, proofFromRows_result, referenceFinish, plonkMaskViewFromMaterial,
    plonkIpaData, honestPlonkMaskView, honestPreIpaMaskView, hp, hc]

/-- Compute every proof field from the real prover inputs and the complete ordered private tape. -/
def execute {actions : ℕ} (generators : Fin 2048 → VestaG) (W U : VestaG)
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 Fp) (tape : Fin (fieldSampleCount actions) → Fp) :
    ProofString (plonkProofShape actions 11) Fp VestaG :=
  let urs : URS VestaG := ⟨11, generators, W, U⟩
  let pub := publicPolynomials instances fixed sigma
  let tapes := executionTapes tape
  let prepared := material vk instances fixed sigma witness ch tapes.1
  finish urs vk pub ch prepared tapes.2

/-- The executable preparation and assembly compute the reference prover's complete proof. -/
theorem execute_result {actions : ℕ} (generators : Fin 2048 → VestaG) (W U : VestaG)
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG)
    (instances : Fin actions → Fin 2048 → Fp) (fixed : Fin 29 → Fin 2048 → Fp)
    (sigma : Fin 15 → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 Fp) (tape : Fin (fieldSampleCount actions) → Fp) :
    execute generators W U vk instances fixed sigma witness ch tape =
      plonkReferenceProofFromTape (⟨11, generators, W, U⟩ : URS VestaG) rfl vk
        (plonkPublicPolynomialsFromRows instances fixed sigma) witness ch tape := by
  let pub := plonkPublicPolynomialsFromRows instances fixed sigma
  let construct := plonkTotalColumnConstructor vk pub witness ch
  let urs : URS VestaG := ⟨11, generators, W, U⟩
  let observe := fun tapes :
      (Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) ×
        (Fin (ipaSampleCount 11) → Fp) =>
    referenceFinish urs vk pub ch (plonkMaterialFromTape construct [] tapes.1) tapes.2
  have h := congrArg observe (executionTapes_result construct tape)
  simp only [execute, finish_result, publicPolynomials_result, material_result]
  exact h.symm

end Zcash.Snark.Fixtures.Prover
