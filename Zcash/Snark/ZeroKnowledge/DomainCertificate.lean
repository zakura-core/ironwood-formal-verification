import Zcash.Arithmetic.Domain

/-!
# The evaluation-domain root without a native certificate

The existing domain constant is reused verbatim. Its primitive-root property is proved
from two modular exponentiations checked by Lean's kernel, avoiding the native axiom in
CompElliptic's bundled parameter certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

set_option maxRecDepth 8192

open Zcash.Arithmetic (Fp rootOfUnityFp omegaOf powFast_eq_pow)

/-- The deployed root literal has exact order `2^32`, by kernel-checked field arithmetic. -/
theorem rootOfUnityFp_primitiveRoot : IsPrimitiveRoot rootOfUnityFp (2 ^ 32) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p := 2) (n := 31)
  · rw [← powFast_eq_pow]
    decide +kernel
  · rw [← powFast_eq_pow]
    decide +kernel

/-- Squaring down the same root gives the actual size-`2^k` domain generator. -/
theorem omegaOf_primitiveRoot (k : ℕ) (hk : k ≤ 32) :
    IsPrimitiveRoot (omegaOf k) (2 ^ k) := by
  unfold omegaOf
  rw [powFast_eq_pow]
  apply IsPrimitiveRoot.pow (by positivity) rootOfUnityFp_primitiveRoot
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- Every supported domain row has a distinct evaluation point. -/
theorem omegaOf_rows_injective (k : ℕ) (hk : k ≤ 32) :
    Function.Injective fun row : Fin (2 ^ k) => omegaOf k ^ row.val := by
  intro i j h
  apply Fin.ext
  exact (omegaOf_primitiveRoot k hk).pow_inj i.isLt j.isLt h

end Zcash.Snark.ZeroKnowledge
