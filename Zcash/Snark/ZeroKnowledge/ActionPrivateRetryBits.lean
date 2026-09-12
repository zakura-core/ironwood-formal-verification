import Zcash.Snark.ZeroKnowledge.ActionOracleRetrySource
import Zcash.Snark.ZeroKnowledge.RawBits

/-!
# The full private retry prefix as a fixed bit string

The complete candidate tape in the finite PRNG game has exactly
`512 * budget * (148m + 46)` bits. Grouping these into consecutive attempt
blocks and little-endian 512-bit words is an explicit computable equivalence.
Uniform bits give the exact uniform raw prefix used by the comparison theorem.
This input-capacity statement is not a machine running-time bound.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Total fixed bit capacity of the private prefix covering every available attempt. -/
def actionPrivateRetryBitCount (actions budget : ℕ) : ℕ :=
  budget * fieldSampleCount actions * 512

/-- Expose the reference's exact per-attempt draw count in the total bit capacity. -/
theorem actionPrivateRetryBitCount_eq (actions budget : ℕ) :
    actionPrivateRetryBitCount actions budget = 512 * budget * (148 * actions + 46) := by
  simp only [actionPrivateRetryBitCount, fieldSampleCount]
  ring

/-- Consecutive raw words grouped first by attempt, then by word within that attempt. -/
def actionPrivateRetryRawEquiv (actions budget : ℕ) :
    RawFieldTape (budget * fieldSampleCount actions) ≃ RawPrivateRetryTape actions budget :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin challengeDigestCard))).trans
    (Equiv.curry (Fin budget) (Fin (fieldSampleCount actions)) (Fin challengeDigestCard))

/-- A canonical fixed-bit encoding of the whole raw private retry prefix. -/
def actionPrivateRetryBitsEquiv (actions budget : ℕ) :
    (Fin (actionPrivateRetryBitCount actions budget) → Bool) ≃ RawPrivateRetryTape actions budget :=
  (rawBitsTapeEquiv (budget * fieldSampleCount actions)).trans (actionPrivateRetryRawEquiv actions budget)

/-- Uniform prefix bits reproduce exactly the whole uniform raw private source, without extra sampling bias. -/
theorem uniformActionPrivateRetryBits (actions budget : ℕ) :
    (PMF.uniformOfFintype (Fin (actionPrivateRetryBitCount actions budget) → Bool)).map
        (actionPrivateRetryBitsEquiv actions budget) =
      PMF.uniformOfFintype (RawPrivateRetryTape actions budget) :=
  Zcash.map_uniformOfFintype_equiv _

end Zcash.Snark.ZeroKnowledge
