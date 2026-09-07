import CompElliptic.Encodings.Pasta
import Zcash.Snark.Core.Vesta

/-!
# The specified proof encodings

Each scalar is its canonical 32-byte little-endian field representative. Each
nonidentity Vesta point uses its affine x-coordinate with y-parity in bit 255.
The proof writer requests fresh randomness on the identity before writing bytes.
These encodings concern proof output; they do not implement Fiat–Shamir hashing.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)

/-- A canonical scalar representative fits in the specified 32-byte proof item. -/
theorem scalarRepresentative_lt_two_pow_256 (value : Fp) : value.val < 2 ^ 256 :=
  (ZMod.val_lt value).trans (by decide : scalarFieldOrder < 2 ^ 256)

/-- The specified canonical little-endian scalar encoding. -/
def plonkScalarCodec (value : Fp) : List UInt8 :=
  (CompElliptic.I2LEOSP 256 ⟨value.val, scalarRepresentative_lt_two_pow_256 value⟩).toList

/-- Every encoded scalar contributes exactly 32 proof bytes. -/
theorem plonkScalarCodec_length (value : Fp) : (plonkScalarCodec value).length = 32 := by
  simp only [plonkScalarCodec, Vector.length_toList]

/-- The specified compressed Vesta encoding, with the prover's identity failure. -/
def plonkPointCodec (point : VestaG) : Option (List UInt8) :=
  if point = 0 then none else some (CompElliptic.toBytes point).toList

/-- The point writer fails exactly on the identity. -/
theorem plonkPointCodec_none_iff (point : VestaG) : plonkPointCodec point = none ↔ point = 0 := by
  simp only [plonkPointCodec]
  split <;> simp_all

/-- A nonidentity point is encoded by the existing canonical Pasta point encoder. -/
theorem plonkPointCodec_of_ne_zero (point : VestaG) (hpoint : point ≠ 0) :
    plonkPointCodec point = some (CompElliptic.toBytes point).toList := by
  simp only [plonkPointCodec, hpoint, ↓reduceIte]

/-- Every successfully encoded point contributes exactly 32 proof bytes. -/
theorem plonkPointCodec_length (point : VestaG) (bytes : List UInt8)
    (hencoded : plonkPointCodec point = some bytes) : bytes.length = 32 := by
  by_cases hpoint : point = 0
  · simp only [plonkPointCodec, hpoint, ↓reduceIte, reduceCtorEq] at hencoded
  · have hbytes : (CompElliptic.toBytes point).toList = bytes := by
      simpa only [plonkPointCodec, hpoint, ↓reduceIte, Option.some.injEq] using hencoded
    simpa only [Vector.length_toList] using (congrArg List.length hbytes).symm

end Zcash.Snark.ZeroKnowledge
