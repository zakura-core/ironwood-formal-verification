import Zcash.Arithmetic.Domain

/-!
# The evaluation-domain root without a native certificate

The domain constant and its kernel-checked primitive-root property are shared with
the arithmetic and compiler layers. These names preserve the zero-knowledge API
without duplicating the root proof or using CompElliptic's native certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (rootOfUnityFp omegaOf)

/-- The deployed root literal has exact order `2^32`, by kernel-checked field arithmetic. -/
theorem rootOfUnityFp_primitiveRoot : IsPrimitiveRoot rootOfUnityFp (2 ^ 32) :=
  Zcash.Arithmetic.rootOfUnityFp_primitiveRoot

/-- Squaring down the same root gives the actual size-`2^k` domain generator. -/
theorem omegaOf_primitiveRoot (k : ℕ) (hk : k ≤ 32) :
    IsPrimitiveRoot (omegaOf k) (2 ^ k) :=
  Zcash.Arithmetic.omegaOf_isPrimitiveRoot k hk

/-- Every supported domain row has a distinct evaluation point. -/
theorem omegaOf_rows_injective (k : ℕ) (hk : k ≤ 32) :
    Function.Injective fun row : Fin (2 ^ k) => omegaOf k ^ row.val :=
  Zcash.Arithmetic.omegaOf_powers_injective k hk

end Zcash.Snark.ZeroKnowledge
