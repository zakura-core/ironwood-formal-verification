import Zcash.Snark.ZeroKnowledge.PlonkLookupRows
import Zcash.Snark.ZeroKnowledge.PermutationPolynomialRows

/-!
# The honest proof's permutation columns and terminal rotations

The actual proof-string records match the polynomial row theorem's next and terminal
rotations. The inverse-sixth-power factor is the retained row 2042, using the
kernel-checked root-of-unity certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial

/-- The terminal query at the first row evaluates at the retained row 2042. -/
theorem plonkTerminalFactor : (omegaOf 11 ^ 6)⁻¹ = omegaOf 11 ^ 2042 := by
  have hroot : IsPrimitiveRoot (omegaOf 11) 2048 := omegaOf_primitiveRoot 11 (by decide)
  symm
  simpa only [hroot.pow_eq_one, _root_.one_mul] using
    pow_sub₀ (omegaOf 11) (hroot.ne_zero (by decide)) (show 6 ≤ 2048 by decide)

/-- The proof string's product record uses the checked next/terminal polynomial rotations. -/
theorem plonkPolynomialClaimProof_permutationSetEvals {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (a : Fin actions) (s : Fin 3) :
    (plonkPolynomialClaimProof (k := k) (G := G) pub rows).permutationSetEvals a s =
      permSetPolys (omegaOf 11) (privateColumnPolynomial rows (.permutationProduct a s))
        (if s.val < 2 then some ((privateColumnPolynomial rows (.permutationProduct a s)).comp
          (C (omegaOf 11 ^ 2042) * X)) else none) := by
  simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString, plonkRotatedColumn_zero]
  simp only [plonkRotatedColumn, plonkQueryFactors, permSetPolys]
  rw [plonkTerminalFactor]
  rfl

end Zcash.Snark.ZeroKnowledge
