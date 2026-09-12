import Zcash.Snark.ZeroKnowledge.PointEncodingCost
import Zcash.Snark.ZeroKnowledge.ListCollectedCost

/-!
# Counted complete transcript-byte construction

Every point uses both affine coordinates, every scalar uses its canonical
representative, and each challenge is the original single marker. The full
flatten pays for producing and copying every byte in the original order.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Encode one stored transcript item with its tag and complete payload cost. -/
def transcriptElementBytesCosted (read : ℕ) : TranscriptElt Fp VestaG → List UInt8 × ℕ
  | .point point =>
    let bytes := vestaAffineCodecCosted (point, read + 1)
    (0x01 :: bytes.1, bytes.2 + 2)
  | .scalar scalar =>
    let bytes := plonkScalarCodecCosted (scalar, read + 1)
    (0x02 :: bytes.1, bytes.2 + 2)
  | .challenge => ([0x00], read + 2)

/-- All tags and payload bytes agree with the actual typed-transcript encoder. -/
theorem transcriptElementBytesCosted_result (read : ℕ) (element : TranscriptElt Fp VestaG) :
    (transcriptElementBytesCosted read element).1 = transcriptElementBytes element := by
  cases element <;> simp only [transcriptElementBytesCosted, transcriptElementBytes,
    vestaAffineCodecCosted_result, plonkScalarCodecCosted_result]

/-- Every produced item has at most the actual 65-byte point encoding width. -/
theorem transcriptElementBytesCosted_length_le (read : ℕ) (element : TranscriptElt Fp VestaG) :
    (transcriptElementBytesCosted read element).1.length ≤ 65 := by
  rw [transcriptElementBytesCosted_result]
  cases element <;> simp [transcriptElementBytes, vestaAffineCodec_length, plonkScalarCodec_length]

/-- Complete per-item cost, including the larger affine payload and its tag. -/
theorem transcriptElementBytesCosted_cost_le (read : ℕ) (element : TranscriptElt Fp VestaG) :
    (transcriptElementBytesCosted read element).2 ≤ 64 * (read + 71) + 2087 := by
  cases element with
  | point point =>
    have h := vestaAffineCodecCosted_cost_le (point, read + 1)
    dsimp only [transcriptElementBytesCosted]
    omega
  | scalar scalar =>
    have h := plonkScalarCodecCosted_cost_le (scalar, read + 1)
    dsimp only [transcriptElementBytesCosted]
    omega
  | challenge =>
    dsimp only [transcriptElementBytesCosted]
    omega

/-- Materialize every byte of the original transcript, paying for all concatenated output cells. -/
def transcriptBytesCosted (read : ℕ) (elements : List (TranscriptElt Fp VestaG)) : List UInt8 × ℕ :=
  flatMapListCosted (transcriptElementBytesCosted read) elements

/-- The complete materialized byte string is exactly the original hash input. -/
theorem transcriptBytesCosted_result (read : ℕ) (elements : List (TranscriptElt Fp VestaG)) :
    (transcriptBytesCosted read elements).1 = transcriptBytes elements := by
  simp only [transcriptBytesCosted, flatMapListCosted_result, transcriptElementBytesCosted_result,
    transcriptBytes]

/-- Transcript production is linear in the already materialized item count at fixed primitive prices. -/
theorem transcriptBytesCosted_cost_le (read : ℕ) (elements : List (TranscriptElt Fp VestaG)) :
    (transcriptBytesCosted read elements).2 ≤ elements.length * (64 * (read + 71) + 2154) + 1 := by
  have h := flatMapListCosted_cost_le_sum (transcriptElementBytesCosted read) elements
    (fun _ => 64 * (read + 71) + 2087) (fun _ => 65)
    (fun element _ => transcriptElementBytesCosted_cost_le read element)
    (fun element _ => transcriptElementBytesCosted_length_le read element)
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul] using h

end Zcash.Snark.ZeroKnowledge
