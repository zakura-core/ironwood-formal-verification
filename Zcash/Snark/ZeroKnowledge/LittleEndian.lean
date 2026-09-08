import Zcash.Snark.ZeroKnowledge.ProofEncoding

/-!
# Exact little-endian encoding and decoding

The existing integer encoder has a left inverse, including at lengths not
divisible by eight. In particular, the specified 32-byte scalar encoding is
injective. Transcript byte separation can therefore use the actual encoder.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The first `count` radix digits reconstruct exactly the corresponding remainder. -/
theorem ofDigits_div_pow_mod (base count value : ℕ) :
    Nat.ofDigits base (List.ofFn (fun i : Fin count => value / base ^ i.val % base)) =
      value % base ^ count := by
  induction count generalizing value with
  | zero => simp only [List.ofFn_zero, Nat.ofDigits_nil, pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ',
      ← Nat.div_div_eq_div_mul]
    rw [ih, Nat.mod_mul]

/-- Decoding the existing fixed-width encoder recovers its in-range input integer. -/
theorem leos2ip_i2leosp (bits : ℕ) (value : Fin (2 ^ bits)) :
    CompElliptic.LEOS2IP (CompElliptic.I2LEOSP bits value) = value.val := by
  have hbound : value.val < 256 ^ ((bits + 7) / 8) := by
    apply value.isLt.trans_le
    rw [show (256 : ℕ) = 2 ^ 8 from by decide, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  simp only [CompElliptic.LEOS2IP, CompElliptic.I2LEOSP, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, UInt8.toNat_ofNat',
    show (2 : ℕ) ^ 8 = 256 from by decide, Nat.mod_mod]
  rw [ofDigits_div_pow_mod, Nat.mod_eq_of_lt hbound]

/-- The actual byte-list encoder is injective on its fixed-width integer domain. -/
theorem i2leosp_toList_injective (bits : ℕ) :
    Function.Injective (fun value : Fin (2 ^ bits) => (CompElliptic.I2LEOSP bits value).toList) := by
  intro left right h
  have hd := congrArg (fun bytes : List UInt8 => Nat.ofDigits 256 (bytes.map UInt8.toNat)) h
  change CompElliptic.LEOS2IP (CompElliptic.I2LEOSP bits left) =
    CompElliptic.LEOS2IP (CompElliptic.I2LEOSP bits right) at hd
  rw [leos2ip_i2leosp, leos2ip_i2leosp] at hd
  exact Fin.ext hd

/-- Canonical scalar bytes identify exactly one field value. -/
theorem plonkScalarCodec_injective : Function.Injective plonkScalarCodec := by
  intro left right h
  have hv := congrArg Fin.val (i2leosp_toList_injective 256 h)
  exact ZMod.val_injective _ hv

end Zcash.Snark.ZeroKnowledge
