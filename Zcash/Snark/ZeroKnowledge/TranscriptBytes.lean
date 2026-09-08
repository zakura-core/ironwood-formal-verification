import Zcash.Snark.ZeroKnowledge.LittleEndian
import Zcash.Snark.Verifier.FiatShamir

/-!
# The specified Fiat–Shamir transcript bytes

Scalars absorb a `0x02` tag and their canonical 32 bytes. Points absorb a `0x01`
tag and both 32-byte affine coordinates. A squeeze absorbs only `0x00`; its
result is not appended. This encoding is distinct from compressed proof output.

The encoding is total on the model's coordinate pairs. It does not decide
whether a point may be emitted: the existing attempt observer performs its
identity check before emitting and absorbing a private point.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompElliptic.Fields.Pasta (VestaBaseField PALLAS_SCALAR_CARD)

/-- A Vesta affine coordinate fits in its specified 32-byte transcript item. -/
theorem vestaCoordinate_lt_two_pow_256 (value : VestaBaseField) : value.val < 2 ^ 256 :=
  (ZMod.val_lt value).trans (by decide : PALLAS_SCALAR_CARD < 2 ^ 256)

/-- The canonical little-endian encoding of one affine coordinate. -/
def vestaCoordinateCodec (value : VestaBaseField) : List UInt8 :=
  (CompElliptic.I2LEOSP 256 ⟨value.val, vestaCoordinate_lt_two_pow_256 value⟩).toList

/-- Every coordinate has exactly 32 bytes. -/
theorem vestaCoordinateCodec_length (value : VestaBaseField) : (vestaCoordinateCodec value).length = 32 := by
  simp only [vestaCoordinateCodec, Vector.length_toList]

/-- Equal coordinate bytes identify equal base-field values. -/
theorem vestaCoordinateCodec_injective : Function.Injective vestaCoordinateCodec := by
  intro left right h
  have hv := congrArg Fin.val (i2leosp_toList_injective 256 h)
  exact ZMod.val_injective _ hv

/-- The transcript absorbs both affine coordinates in x-then-y order. -/
def vestaAffineCodec (point : VestaG) : List UInt8 :=
  vestaCoordinateCodec point.x ++ vestaCoordinateCodec point.y

/-- The affine payload has 64 bytes before its point tag. -/
theorem vestaAffineCodec_length (point : VestaG) : (vestaAffineCodec point).length = 64 := by
  simp only [vestaAffineCodec, List.length_append, vestaCoordinateCodec_length]

/-- The actual affine payload identifies exactly one Vesta point. -/
theorem vestaAffineCodec_injective : Function.Injective vestaAffineCodec := by
  intro left right h
  have hp := List.append_inj h (by rw [vestaCoordinateCodec_length, vestaCoordinateCodec_length])
  exact CompElliptic.CurveForms.ShortWeierstrass.SWPoint.ext_pair
    (Prod.ext (vestaCoordinateCodec_injective hp.1) (vestaCoordinateCodec_injective hp.2))

/-- The specified domain tag and payload of one transcript element. -/
def transcriptElementBytes : TranscriptElt Fp VestaG → List UInt8
  | .point point => 0x01 :: vestaAffineCodec point
  | .scalar scalar => 0x02 :: plonkScalarCodec scalar
  | .challenge => [0x00]

/-- Concatenate all element encodings in the verifier's absorb order. -/
def transcriptBytes (elements : List (TranscriptElt Fp VestaG)) : List UInt8 :=
  elements.flatMap transcriptElementBytes

/-- Extending a typed transcript appends exactly the corresponding bytes. -/
theorem transcriptBytes_append (left right : List (TranscriptElt Fp VestaG)) :
    transcriptBytes (left ++ right) = transcriptBytes left ++ transcriptBytes right :=
  List.flatMap_append

/-- An empty byte transcript has no hidden absorbed elements. -/
theorem transcriptBytes_eq_nil_iff (elements : List (TranscriptElt Fp VestaG)) :
    transcriptBytes elements = [] ↔ elements = [] := by
  cases elements with
  | nil => simp [transcriptBytes]
  | cons element rest => cases element <;> simp [transcriptBytes, transcriptElementBytes]

/-- The tag and fixed payload width separate the first element from every possible suffix. -/
theorem transcriptElementBytes_append_injective
    (left right : TranscriptElt Fp VestaG) (leftRest rightRest : List UInt8)
    (h : transcriptElementBytes left ++ leftRest = transcriptElementBytes right ++ rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases left <;> cases right <;> simp [transcriptElementBytes] at h
  · have hp := List.append_inj h (by rw [vestaAffineCodec_length, vestaAffineCodec_length])
    exact ⟨congrArg TranscriptElt.point (vestaAffineCodec_injective hp.1), hp.2⟩
  · have hs := List.append_inj h (by rw [plonkScalarCodec_length, plonkScalarCodec_length])
    exact ⟨congrArg TranscriptElt.scalar (plonkScalarCodec_injective hs.1), hs.2⟩
  · exact ⟨rfl, h⟩

/-- Distinct typed transcripts have distinct specified byte strings. -/
theorem transcriptBytes_injective : Function.Injective transcriptBytes := by
  intro left
  induction left with
  | nil =>
    intro right h
    exact ((transcriptBytes_eq_nil_iff right).mp h.symm).symm
  | cons head rest ih =>
    intro right h
    cases right with
    | nil =>
      have hn := (transcriptBytes_eq_nil_iff (head :: rest)).mp h
      cases hn
    | cons head' rest' =>
      have hs := transcriptElementBytes_append_injective head head' _ _ h
      exact congrArg₂ List.cons hs.1 (ih hs.2)

/-- The fixed BLAKE2b personalization is a separate sixteen-byte domain parameter. -/
def halo2TranscriptPersonalization : List UInt8 := "Halo2-Transcript".toUTF8.data.toList

/-- The personalization has the exact BLAKE2b parameter width. -/
theorem halo2TranscriptPersonalization_length : halo2TranscriptPersonalization.length = 16 := by decide

end Zcash.Snark.ZeroKnowledge
