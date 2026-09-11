import Zcash.Snark.ZeroKnowledge.PlonkOpening

/-!
# The pinned query orders as literal tables

`plonkFixedQueryOrder` and `plonkAdviceQueryOrder` store their entries in arrays, so the prover
replay reads each entry directly. `simp` does not evaluate an array read at a numeral index, but
it does evaluate the `![…]` literal. Proofs that need concrete entries rewrite with the
equalities below.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The fixed-query order equals its literal table, so `simp` can read its 29 entries. -/
theorem plonkFixedQueryOrder_eq_vecCons : plonkFixedQueryOrder =
    ![3, 0, 11, 4, 5, 6, 7, 8, 9, 10, 12, 1, 2, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 23, 24, 25, 26, 27, 28] := by
  funext query
  fin_cases query <;> rfl

/-- The advice-query order equals its literal table, so `simp` can read its 25 column-and-rotation
pairs. -/
theorem plonkAdviceQueryOrder_eq_vecCons : plonkAdviceQueryOrder =
    ![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
      (9, 1), (9, 2), (2, 1), (3, 1), (4, 1), (5, 1), (0, 1), (1, 1), (7, 1), (8, 1),
      (6, 2), (1, 2), (6, 1), (7, 2), (8, 2)] := by
  funext query
  fin_cases query <;> rfl

end Zcash.Snark.ZeroKnowledge
