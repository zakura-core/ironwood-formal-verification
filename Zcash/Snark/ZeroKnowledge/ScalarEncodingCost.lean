import Zcash.Snark.ZeroKnowledge.ProofEncoding
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-!
# Counted canonical scalar-byte production

The encoder materializes every byte through the original little-endian formula.
Bounded-width natural multiplication, division, remainder, and byte conversion
each cost one structural unit. Every byte retains the complete supplied scalar
access cost. This is a primitive-cost model, not a machine-code correspondence.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
set_option exponentiation.threshold 1024

/-- Compute one original byte, retaining the entire input access and denominator construction. -/
def i2leosp256ByteCosted (value : Fin (2 ^ 256) × ℕ) (index : Fin 32) : UInt8 × ℕ :=
  let denominator := fieldPowerCosted 1 (256 : ℕ) index.val
  (UInt8.ofNat (value.1.val / denominator.1 % 256), value.2 + denominator.2 + 4)

/-- Each counted byte is the original little-endian byte at the same index. -/
theorem i2leosp256ByteCosted_result (value : Fin (2 ^ 256) × ℕ) (index : Fin 32) :
    (i2leosp256ByteCosted value index).1 = UInt8.ofNat (value.1.val / 256 ^ index.val % 256) := by
  simp only [i2leosp256ByteCosted, fieldPowerCosted_result]

/-- The fixed byte index bounds all denominator construction and byte arithmetic. -/
theorem i2leosp256ByteCosted_cost_le (value : Fin (2 ^ 256) × ℕ) (index : Fin 32) :
    (i2leosp256ByteCosted value index).2 ≤ value.2 + 67 := by
  have hi := index.isLt
  simp only [i2leosp256ByteCosted, fieldPowerCosted_cost]
  omega

/-- Materialize the complete original 32-byte integer encoding. -/
def i2leosp256Costed (value : Fin (2 ^ 256) × ℕ) : List UInt8 × ℕ :=
  ofFnCosted (i2leosp256ByteCosted value)

/-- The materialized bytes are exactly the existing canonical integer encoding. -/
theorem i2leosp256Costed_result (value : Fin (2 ^ 256) × ℕ) :
    (i2leosp256Costed value).1 = (CompElliptic.I2LEOSP 256 value.1).toList := by
  simp only [i2leosp256Costed, ofFnCosted_result, i2leosp256ByteCosted_result,
    CompElliptic.I2LEOSP, Vector.toList_ofFn]

/-- The integer encoding bound includes every input access and output-cell construction. -/
theorem i2leosp256Costed_cost_le (value : Fin (2 ^ 256) × ℕ) :
    (i2leosp256Costed value).2 ≤ 32 * (value.2 + 68) + 1025 := by
  have h := ofFnCosted_cost_le (i2leosp256ByteCosted value) (value.2 + 67)
    (i2leosp256ByteCosted_cost_le value)
  exact h

/-- Encode the actual protocol scalar, charging also for reading its canonical representative. -/
def plonkScalarCodecCosted (value : Fp × ℕ) : List UInt8 × ℕ :=
  i2leosp256Costed (⟨value.1.val, scalarRepresentative_lt_two_pow_256 value.1⟩, value.2 + 1)

/-- Scalar cost erasure is the exact codec used by the proof and transcript observers. -/
theorem plonkScalarCodecCosted_result (value : Fp × ℕ) :
    (plonkScalarCodecCosted value).1 = plonkScalarCodec value.1 :=
  i2leosp256Costed_result _

/-- Complete scalar encoding cost, including canonical-representative and supplied value reads. -/
theorem plonkScalarCodecCosted_cost_le (value : Fp × ℕ) :
    (plonkScalarCodecCosted value).2 ≤ 32 * (value.2 + 69) + 1025 :=
  i2leosp256Costed_cost_le _

end Zcash.Snark.ZeroKnowledge
