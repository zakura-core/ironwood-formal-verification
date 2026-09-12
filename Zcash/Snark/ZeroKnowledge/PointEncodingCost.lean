import Zcash.Snark.ZeroKnowledge.ScalarEncodingCost
import Zcash.Snark.ZeroKnowledge.TranscriptBytes
import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Counted proof-point and affine-transcript encodings

The two encodings remain distinct: compressed proof points reject the identity,
while transcript points contain both coordinates. Coordinate and representative
reads, bounded-width sign-bit arithmetic, every produced byte, and list copying
are counted. Point equality has an explicit primitive price.
-/

namespace Zcash.Snark.ZeroKnowledge
open CompElliptic.Fields.Pasta (VestaBaseField)
set_option exponentiation.threshold 1024

/-- Encode one canonical affine coordinate with its complete supplied access cost. -/
def vestaCoordinateCodecCosted (value : VestaBaseField × ℕ) : List UInt8 × ℕ :=
  i2leosp256Costed (⟨value.1.val, vestaCoordinate_lt_two_pow_256 value.1⟩, value.2 + 1)

/-- Coordinate encoding erases to the original transcript codec. -/
theorem vestaCoordinateCodecCosted_result (value : VestaBaseField × ℕ) :
    (vestaCoordinateCodecCosted value).1 = vestaCoordinateCodec value.1 :=
  i2leosp256Costed_result _

/-- Complete canonical-coordinate production has the same bounded-width byte cost. -/
theorem vestaCoordinateCodecCosted_cost_le (value : VestaBaseField × ℕ) :
    (vestaCoordinateCodecCosted value).2 ≤ 32 * (value.2 + 69) + 1025 :=
  i2leosp256Costed_cost_le _

/-- Produce both affine coordinates and concatenate them in the original x-then-y order. -/
def vestaAffineCodecCosted (point : VestaG × ℕ) : List UInt8 × ℕ :=
  let x := vestaCoordinateCodecCosted (point.1.x, point.2 + 1)
  let y := vestaCoordinateCodecCosted (point.1.y, point.2 + 1)
  let joined := appendListCosted x.1 y.1
  (joined.1, x.2 + y.2 + joined.2 + 2)

/-- The complete affine payload is exactly the original transcript payload. -/
theorem vestaAffineCodecCosted_result (point : VestaG × ℕ) :
    (vestaAffineCodecCosted point).1 = vestaAffineCodec point.1 := by
  simp only [vestaAffineCodecCosted, appendListCosted_result, vestaCoordinateCodecCosted_result,
    vestaAffineCodec]

/-- Both coordinate productions and the complete concatenation are included. -/
theorem vestaAffineCodecCosted_cost_le (point : VestaG × ℕ) :
    (vestaAffineCodecCosted point).2 ≤ 64 * (point.2 + 70) + 2085 := by
  have hx := vestaCoordinateCodecCosted_cost_le (point.1.x, point.2 + 1)
  have hy := vestaCoordinateCodecCosted_cost_le (point.1.y, point.2 + 1)
  simp only [vestaAffineCodecCosted, appendListCosted_cost, vestaCoordinateCodecCosted_result,
    vestaCoordinateCodec_length]
  omega

/-- Run the original identity check and compressed-point byte computation with complete costs. -/
def plonkPointCodecCosted (equal : ℕ) (point : VestaG × ℕ) : Option (List UInt8) × ℕ :=
  if point.1 = 0 then (none, point.2 + equal + 2)
  else
    let representative : Fin (2 ^ 256) :=
      ⟨point.1.x.val + (point.1.y.val % 2) * 2 ^ 255, CompElliptic.encodedInt_lt point.1.x point.1.y⟩
    let bytes := i2leosp256Costed (representative, point.2 + 8)
    (some bytes.1, bytes.2 + equal + 3)

/-- Every compressed byte and the identity-failure branch match the specified proof codec. -/
theorem plonkPointCodecCosted_result (equal : ℕ) (point : VestaG × ℕ) :
    (plonkPointCodecCosted equal point).1 = plonkPointCodec point.1 := by
  by_cases hp : point.1 = 0
  · simp only [plonkPointCodecCosted, plonkPointCodec, hp, ↓reduceIte]
  · simp only [plonkPointCodecCosted, plonkPointCodec, hp, ↓reduceIte, i2leosp256Costed_result,
      CompElliptic.toBytes]

/-- The full proof-point bound also covers an immediate identity failure. -/
theorem plonkPointCodecCosted_cost_le (equal : ℕ) (point : VestaG × ℕ) :
    (plonkPointCodecCosted equal point).2 ≤ 32 * (point.2 + 76) + equal + 1028 := by
  by_cases hp : point.1 = 0
  · simp only [plonkPointCodecCosted, hp, ↓reduceIte]
    omega
  · have h := i2leosp256Costed_cost_le
      (⟨point.1.x.val + (point.1.y.val % 2) * 2 ^ 255,
        CompElliptic.encodedInt_lt point.1.x point.1.y⟩, point.2 + 8)
    simp only [plonkPointCodecCosted, hp, ↓reduceIte]
    omega

end Zcash.Snark.ZeroKnowledge
