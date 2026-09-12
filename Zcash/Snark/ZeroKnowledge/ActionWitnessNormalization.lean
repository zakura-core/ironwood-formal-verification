import Zcash.Circuits.Action.Spec
import Zcash.Snark.ZeroKnowledge.WindowDigits

/-!
# Canonical auxiliary data for an application Action witness

`ActionSpec` uses the five scalar values and the literal Merkle encodings, not
the extracted scalar-window vectors or the auxiliary `(sibling, swap)` function.
A constructor can therefore derive those auxiliary values canonically while
preserving the application statement and every semantic scalar exactly.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits
open Zcash.Circuits.Action
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)

/-- The 85 canonical three-bit digits of the actual scalar value. -/
def canonicalActionScalarWindows (scalar : Fq) : Vector Fp 85 :=
  Vector.ofFn (fun window => ((scalar.val / 8 ^ window.val % 8 : ℕ) : Fp))

/-- Each canonical field window decodes to exactly its natural base-eight digit. -/
theorem canonicalActionScalarWindows_val (scalar : Fq) (window : Fin 85) :
    ((canonicalActionScalarWindows scalar)[window.val]).val = scalar.val / 8 ^ window.val % 8 := by
  simp only [canonicalActionScalarWindows, Vector.getElem_ofFn, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ (by decide : 0 < 8)).trans_le (by norm_num [PALLAS_BASE_CARD]))

/-- All five fixed-base gadgets' window range premises hold for the derived digits. -/
theorem canonicalActionScalarWindows_lt (scalar : Fq) (window : Fin 85) :
    ((canonicalActionScalarWindows scalar)[window.val]).val < 8 := by
  rw [canonicalActionScalarWindows_val]
  exact Nat.mod_lt _ (by decide)

/-- The circuit's scalar extractor recovers the original scalar, including its highest allowed bits. -/
theorem canonicalActionScalarWindows_reconstruct (scalar : Fq) :
    Ecc.MulFixed.FullWidth.windowsScalar (canonicalActionScalarWindows scalar) = scalar := by
  unfold Ecc.MulFixed.FullWidth.windowsScalar
  have hsum : (∑ window ∈ Finset.range 85,
      ((canonicalActionScalarWindows scalar)[window]!).val * 8 ^ window) = scalar.val := by
    calc
      _ = ∑ window ∈ Finset.range 85, (scalar.val / 8 ^ window % 8) * 8 ^ window := by
        apply Finset.sum_congr rfl
        intro window hw
        have hi := Finset.mem_range.mp hw
        rw [getElem!_pos (canonicalActionScalarWindows scalar) window hi,
          canonicalActionScalarWindows_val scalar ⟨window, hi⟩]
      _ = scalar.val % 8 ^ 85 := octalDigits_sum_mod scalar.val 85
      _ = scalar.val := Nat.mod_eq_of_lt ((ZMod.val_lt scalar).trans_le (by norm_num [PALLAS_SCALAR_CARD]))
  rw [hsum]
  exact ZMod.natCast_zmod_val scalar

/-- The sibling and Boolean swap flag selected by the application's literal Merkle encodings. -/
def canonicalActionMerklePath (witness : PrivateWitness) (layer : ℕ) : Fp × Fp :=
  if h : layer < 32 then
    (if witness.merkleSide ⟨layer, h⟩ then (witness.leftEncoding ⟨layer, h⟩ : Fp)
      else (witness.rightEncoding ⟨layer, h⟩ : Fp),
      if witness.merkleSide ⟨layer, h⟩ then 1 else 0)
  else (0, 0)

/-- Derive auxiliary windows and Merkle readings without changing any semantic application input. -/
def normalizeActionWitness (witness : PrivateWitness) : PrivateWitness :=
  { witness with
    rcv := (canonicalActionScalarWindows witness.rcv.2, witness.rcv.2)
    alpha := (canonicalActionScalarWindows witness.alpha.2, witness.alpha.2)
    rivk := (canonicalActionScalarWindows witness.rivk.2, witness.rivk.2)
    rcmOld := (canonicalActionScalarWindows witness.rcmOld.2, witness.rcmOld.2)
    rcmNew := (canonicalActionScalarWindows witness.rcmNew.2, witness.rcmNew.2)
    merklePath := canonicalActionMerklePath witness }

/-- Canonicalizing constructor-only data preserves the complete application specification exactly. -/
theorem normalizeActionWitness_spec_iff (inputs : PublicInputs Fp) (witness : PrivateWitness) :
    ActionSpec inputs (normalizeActionWitness witness) ↔ ActionSpec inputs witness := by
  simp only [ActionSpec, normalizeActionWitness]

end Zcash.Snark.ZeroKnowledge
