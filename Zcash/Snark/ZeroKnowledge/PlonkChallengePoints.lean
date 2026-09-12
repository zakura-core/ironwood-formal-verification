import Zcash.Snark.ZeroKnowledge.PlonkChallenges

/-!
# Sufficient conditions on the two opening points

The four rotations are distinct powers of the size-2048 root of unity. A nonzero `x`
keeps those four points distinct; excluding their collisions with `q` gives five
distinct points. Keeping `x` and `q` outside the row domain keeps every rotation
outside it as well. No exclusions on unrelated challenges are introduced here.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- The rotations `0`, `1`, `-1`, and `-6`, represented modulo the domain size. -/
def plonkRotationExponent : Fin 4 → Fin 2048 := ![0, 1, 2047, 2042]

/-- These four row rotations are distinct modulo 2048. -/
theorem plonkRotationExponent_injective : Function.Injective plonkRotationExponent := by
  decide +kernel

/-- The first four observations are the specified powers of the row-domain root. -/
theorem plonkObservationPoints_prefix (omega x q : Fp)
    (hroot : IsPrimitiveRoot omega 2048) (i : Fin 4) :
    plonkObservationPoints omega x q i.castSucc = x * omega ^ (plonkRotationExponent i).val := by
  have hz : omega ≠ 0 := hroot.ne_zero (by decide)
  have h1 : omega ^ 2047 = omega⁻¹ := by
    simpa only [hroot.pow_eq_one, one_mul, pow_one] using pow_sub₀ omega hz (show 1 ≤ 2048 by decide)
  have h6 : omega ^ 2042 = (omega ^ 6)⁻¹ := by
    simpa only [hroot.pow_eq_one, one_mul] using pow_sub₀ omega hz (show 6 ≤ 2048 by decide)
  fin_cases i <;> simp [plonkObservationPoints, plonkRotationExponent, h1, h6]

/-- The common observation vector appends `q` to the four rotated points. -/
theorem plonkObservationPoints_snoc (omega x q : Fp) (hroot : IsPrimitiveRoot omega 2048) :
    plonkObservationPoints omega x q =
      Fin.snoc (fun i => x * omega ^ (plonkRotationExponent i).val) q := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change q = Fin.snoc (α := fun _ : Fin 5 => Fp)
      (fun j : Fin 4 => x * omega ^ (plonkRotationExponent j).val) q (Fin.last 4)
    rw [Fin.snoc_last]
  · simpa only [Fin.snoc_castSucc] using plonkObservationPoints_prefix omega x q hroot j

/-- A nonzero first point and no cross-point collision give five distinct observations. -/
theorem plonkObservationPoints_injective (omega x q : Fp) (hroot : IsPrimitiveRoot omega 2048)
    (hx : x ≠ 0) (hq : ∀ i : Fin 4, q ≠ x * omega ^ (plonkRotationExponent i).val) :
    Function.Injective (plonkObservationPoints omega x q) := by
  rw [plonkObservationPoints_snoc omega x q hroot]
  apply Fin.snoc_injective_of_injective
  · intro i j hij
    apply plonkRotationExponent_injective
    apply Fin.ext
    exact hroot.pow_inj (plonkRotationExponent i).isLt (plonkRotationExponent j).isLt
      ((mul_left_cancel₀ hx) hij)
  · intro h
    obtain ⟨i, hi⟩ := h
    exact hq i hi.symm

/-- Multiplication by a row-domain root preserves being outside that domain. -/
theorem plonkObservationPoints_away (omega x q : Fp) (hroot : IsPrimitiveRoot omega 2048)
    (hx : x ^ 2048 ≠ 1) (hq : q ^ 2048 ≠ 1) :
    ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints omega x q i ≠ omega ^ j.val := by
  rw [plonkObservationPoints_snoc omega x q hroot]
  have hpow (e : ℕ) : (omega ^ e) ^ 2048 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot.pow_eq_one, one_pow]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j heq
    apply hq
    have hp := congrArg (fun v : Fp => v ^ 2048) heq
    simpa only [Fin.snoc_last, hpow] using hp
  · intro j heq
    apply hx
    have hp := congrArg (fun v : Fp => v ^ 2048) heq
    simpa only [Fin.snoc_castSucc, mul_pow, hpow, mul_one] using hp

/-- A short list of scalar conditions supplies every challenge premise of joint simulation. -/
theorem plonkChallengesGood_of_simple {k : ℕ} (ch : Challenges k Fp)
    (hxi : ch.xi ≠ 0) (hu : ∀ j, ch.ipaRound j ≠ 0) (hx0 : ch.x ≠ 0)
    (hx : ch.x ^ 2048 ≠ 1) (hq : ch.x3 ^ 2048 ≠ 1)
    (hqx : ∀ i : Fin 4, ch.x3 ≠ ch.x * omegaOf 11 ^ (plonkRotationExponent i).val) :
    PlonkChallengesGood ch := by
  have hroot : IsPrimitiveRoot (omegaOf 11) 2048 :=
    omegaOf_primitiveRoot 11 (by decide)
  exact ⟨hxi, hu, hx, plonkObservationPoints_injective _ _ _ hroot hx0 hqx,
    plonkObservationPoints_away _ _ _ hroot hx hq⟩

end Zcash.Snark.ZeroKnowledge
