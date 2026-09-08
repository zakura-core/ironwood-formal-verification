import Zcash.Snark.ZeroKnowledge.ActionWitnessNormalization
import Zcash.Snark.ZeroKnowledge.CanonicalMerklePath

/-!
# Application witness construction conditions

The input starts with `ActionSpec`. Defined Sinsemilla hashes and canonical
Merkle encodings turn its guarded statements into the honest path computation.
The fixed top-level hint program also needs each scalar's natural representative
to fit in one base-field hint. These are input conditions, not assumptions about
proof emission, verifier acceptance, or already-satisfying circuit rows.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Circuits.Sinsemilla.Merkle
open Zcash.Circuits.Sinsemilla.Merkle.CalculateRoot
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- Scalar representatives encodable by the existing one-field `natHint` interface. -/
structure ActionScalarHintBounds (witness : PrivateWitness) : Prop where
  rcv : witness.rcv.2.val < PALLAS_BASE_CARD
  alpha : witness.alpha.2.val < PALLAS_BASE_CARD
  rivk : witness.rivk.2.val < PALLAS_BASE_CARD
  rcmOld : witness.rcmOld.2.val < PALLAS_BASE_CARD
  rcmNew : witness.rcmNew.2.val < PALLAS_BASE_CARD

/-- The literal application left-child encodings, padded outside its 32 layers. -/
def actionWitnessLeftEncoding (witness : PrivateWitness) (index : ℕ) : ℕ :=
  if h : index < 32 then witness.leftEncoding ⟨index, h⟩ else 0

/-- The literal application right-child encodings, padded outside its 32 layers. -/
def actionWitnessRightEncoding (witness : PrivateWitness) (index : ℕ) : ℕ :=
  if h : index < 32 then witness.rightEncoding ⟨index, h⟩ else 0

/-- The application's selected child side, padded outside its 32 layers. -/
def actionWitnessSide (witness : PrivateWitness) (index : ℕ) : Bool :=
  if h : index < 32 then witness.merkleSide ⟨index, h⟩ else false

/-- The application-level input contract for the existing hint-driven witness generator. -/
structure ActionWitnessConstructionConditions (inputs : PublicInputs Fp) (witness : PrivateWitness) : Prop where
  specification : ActionSpec inputs witness
  scalarHints : ActionScalarHintBounds witness
  canonicalLeft : ∀ index, witness.leftEncoding index < PALLAS_BASE_CARD
  canonicalRight : ∀ index, witness.rightEncoding index < PALLAS_BASE_CARD
  ivkDefined : (hashToPoint orchardGenerators.S orchardBases.ivkQ
    (commitIvkChunks witness.akP.x.val witness.nk.val)).isSome
  oldNoteDefined : (hashToPoint orchardGenerators.S orchardBases.noteQ
    (NoteCommit.noteScalars witness.gdOld witness.pkdOld witness.vOld witness.rhoOld witness.psiOld).chunks).isSome
  newNoteDefined : (hashToPoint orchardGenerators.S orchardBases.noteQ
    (NoteCommit.noteScalars witness.gdNew witness.pkdNew witness.vNew inputs.nfOld witness.psiNew).chunks).isSome
  merkleDefined : ∀ index : Fin 32,
    (hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleChunks index.val (witness.leftEncoding index) (witness.rightEncoding index))).isSome

/-- The normalized Merkle witness is exactly the canonical reading of the application encodings. -/
theorem canonicalActionMerklePath_eq_readings (witness : PrivateWitness) :
    canonicalActionMerklePath witness = canonicalMerkleReadings
      (actionWitnessLeftEncoding witness) (actionWitnessRightEncoding witness) (actionWitnessSide witness) := by
  funext index
  by_cases hi : index < 32 <;>
    simp only [canonicalActionMerklePath, canonicalMerkleReadings, actionWitnessLeftEncoding,
      actionWitnessRightEncoding, actionWitnessSide, hi, dite_true, dite_false,
      Bool.false_eq_true, if_false, Nat.cast_zero]

/-- The application's exact root is produced by the honest 32-layer fold under the stated input conditions. -/
theorem actionWitnessConditions_merkleRoot {inputs : PublicInputs Fp} {witness : PrivateWitness}
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (root : Fp)
    (hpath : ExactMerklePathData orchardGenerators orchardBases.merkleQ 0 32 witness.cmOld.x root
      (actionWitnessLeftEncoding witness) (actionWitnessRightEncoding witness) (actionWitnessSide witness)) :
    pathNode orchardGenerators orchardBases.merkleQ 0 (canonicalActionMerklePath witness) witness.cmOld.x 32 = some root := by
  rw [canonicalActionMerklePath_eq_readings]
  apply exactCanonicalMerklePath_pathNode _ _ _ _ _ _ _ _ _ hpath
  · intro index hi
    simpa only [actionWitnessLeftEncoding, dif_pos hi] using conditions.canonicalLeft ⟨index, hi⟩
  · intro index hi
    simpa only [actionWitnessRightEncoding, dif_pos hi] using conditions.canonicalRight ⟨index, hi⟩
  · intro index hi
    simpa only [actionWitnessLeftEncoding, actionWitnessRightEncoding, dif_pos hi, Nat.zero_add] using
      conditions.merkleDefined ⟨index, hi⟩

/-- The existing circuit's two 16-layer computations use the exact application root and anchor equation. -/
theorem actionWitnessConditions_merkleHalves {inputs : PublicInputs Fp} {witness : PrivateWitness}
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (root : Fp)
    (hpath : ExactMerklePathData orchardGenerators orchardBases.merkleQ 0 32 witness.cmOld.x root
      (actionWitnessLeftEncoding witness) (actionWitnessRightEncoding witness) (actionWitnessSide witness)) :
    ∃ middle,
      pathNode orchardGenerators orchardBases.merkleQ 0 (canonicalActionMerklePath witness) witness.cmOld.x 16 = some middle ∧
      pathNode orchardGenerators orchardBases.merkleQ 16 (fun index => canonicalActionMerklePath witness (16 + index))
        middle 16 = some root := by
  have h := actionWitnessConditions_merkleRoot conditions root hpath
  have hsplit := pathNode_append orchardGenerators orchardBases.merkleQ 0
    (canonicalActionMerklePath witness) witness.cmOld.x 16 16
  rw [hsplit] at h
  cases hm : pathNode orchardGenerators orchardBases.merkleQ 0
      (canonicalActionMerklePath witness) witness.cmOld.x 16 with
  | none => simp [hm] at h
  | some middle =>
    refine ⟨middle, rfl, ?_⟩
    simpa only [hm, Option.bind_some, Nat.zero_add] using h

/-- Application validity and the explicit constructor conditions supply the existing honest-prover preconditions. -/
theorem actionWitnessConditions_proverAssumptions {inputs : PublicInputs Fp} {witness : PrivateWitness}
    (conditions : ActionWitnessConstructionConditions inputs witness) (hints : ProverHint Fp) :
    Circuit.ProverAssumptionsPost orchardGenerators orchardBases ()
      (combine inputs (normalizeActionWitness witness)) hints := by
  rcases conditions.specification with
    ⟨hcm, hgd, hak, hpkd, hgdNew, hpkdNew, hvOld, hvNew, hcv, hnf, hrk,
      hivk, hnoteOld, hnoteNew, hpath, hvalue, hspend, houtput, hcross⟩
  have hsign : witness.sign = 1 ∨ witness.sign = -1 := hcv.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hcommit :
      (witness.sign = 1 → (⟨inputs.cvX, inputs.cvY⟩ : Point Fp) =
        (witness.magnitude.val : Fq) • orchardBases.valueCommitV + witness.rcv.2 • orchardBases.valueCommitR) ∧
      (witness.sign = -1 → (⟨inputs.cvX, inputs.cvY⟩ : Point Fp) =
        -(witness.magnitude.val : Fq) • orchardBases.valueCommitV + witness.rcv.2 • orchardBases.valueCommitR) := by
    rcases hcv.2 with ⟨hs, hc⟩ | ⟨hs, hc⟩
    · refine ⟨fun _ => hc, ?_⟩
      intro hn
      have hbad : (1 : Fp) = -1 := hs.symm.trans hn
      exact False.elim ((by decide : (1 : Fp) ≠ -1) hbad)
    · refine ⟨?_, fun _ => hc⟩
      intro hp
      have hbad : (1 : Fp) = -1 := hp.symm.trans hs
      exact False.elim ((by decide : (1 : Fp) ≠ -1) hbad)
  obtain ⟨ivkPoint, hivkPoint⟩ := Option.isSome_iff_exists.mp conditions.ivkDefined
  obtain ⟨oldPoint, holdPoint⟩ := Option.isSome_iff_exists.mp conditions.oldNoteDefined
  obtain ⟨newPoint, hnewPoint⟩ := Option.isSome_iff_exists.mp conditions.newNoteDefined
  obtain ⟨ivk, hivkHash, hpkdIvk⟩ := hivk
  have hIvk := hivkHash ivkPoint hivkPoint
  obtain ⟨root, hrootPath, hanchor⟩ := hpath
  obtain ⟨middle, hmiddle, hroot⟩ := actionWitnessConditions_merkleHalves conditions root hrootPath
  constructor
  · change Circuit.ProverAssumptionsCore orchardGenerators orchardBases (combine inputs (normalizeActionWitness witness))
    simp only [Circuit.ProverAssumptionsCore, combine, normalizeActionWitness]
    refine ⟨hcm, hgd, hak, hpkd, hgdNew, hpkdNew,
      canonicalActionScalarWindows_lt witness.rcv.2, canonicalActionScalarWindows_lt witness.alpha.2,
      canonicalActionScalarWindows_lt witness.rivk.2, canonicalActionScalarWindows_lt witness.rcmOld.2,
      canonicalActionScalarWindows_lt witness.rcmNew.2, hcv.1, hsign, hvOld, hvNew,
      ⟨middle, hmiddle, root, hroot, hanchor⟩,
      ⟨ivkPoint, hivkPoint, ?_⟩, ⟨oldPoint, holdPoint, hnoteOld oldPoint holdPoint⟩,
      ⟨newPoint, hnewPoint, hnoteNew newPoint hnewPoint⟩, hcommit, hnf, hrk, hvalue, hspend, houtput⟩
    simpa only [hIvk] using hpkdIvk
  · change inputs.disableCrossAddress = 0 ∨ (witness.gdOld = witness.gdNew ∧ witness.pkdOld = witness.pkdNew)
    by_cases hz : inputs.disableCrossAddress = 0
    · exact Or.inl hz
    · exact Or.inr (hcross hz)

end Zcash.Snark.ZeroKnowledge
