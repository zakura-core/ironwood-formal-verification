import Zcash.Snark.ZeroKnowledge.ColumnPrefix
import Zcash.Snark.ZeroKnowledge.PlonkColumnReads
import Zcash.Snark.ZeroKnowledge.PlonkConstruction

/-!
# The concrete pre-product state is fixed before beta and gamma

Run the total reference construction on one fixed replacement-row tape. Its advice
and lookup permutation columns depend on `theta`, but not on the later product
challenges. The denominator coefficients can therefore be fixed before fresh
`beta` and `gamma` are sampled.

Failed sorts are still replaced by zero in this total comparison computation.
Completed partial attempts agree with it on the same tape; that pointwise equality
does not condition either challenge or tape distributions on completion.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Run the total comparison construction on the fixed `126m` replacement-row tape. -/
def plonkTotalColumnRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) : ColumnHistory 2048 :=
  columnRowsFromTape (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch)) []
    (tape ∘ Fin.cast (plonkColumnSteps_row_samples (plonkTotalColumnConstructor vk pub witness ch)))

/-- The total computation produces all scheduled columns even if a sort failed. -/
theorem plonkTotalColumnRows_length {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    (plonkTotalColumnRows vk pub witness ch tape).length = 22 * actions := by
  simp only [plonkTotalColumnRows, columnRowsFromTape_length, plonkColumnSteps_length]

/-- The fixed-size uniform tape realizes exactly the sequential row law used by the joint simulation. -/
theorem uniformTapePlonkTotalColumnRows {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp) :
    (PMF.uniformOfFintype (Fin (126 * actions) → Fp)).map (plonkTotalColumnRows vk pub witness ch) =
      idealColumnRows (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch)) [] :=
  uniformTapeColumnRows_cast _ (plonkColumnSteps_row_samples (plonkTotalColumnConstructor vk pub witness ch)) []

/-- A completed reference attempt is exactly the total comparison on the same tape. -/
theorem plonkColumnAttempt_eq_totalRows_of_complete {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true) :
    (plonkColumnAttempt vk pub witness ch tape).columns = plonkTotalColumnRows vk pub witness ch tape :=
  plonkColumnAttempt_eq_of_complete vk pub witness ch tape hcomplete

/-- Every constructor before the products uses only the earlier `theta` challenge. -/
theorem plonkTotalColumnConstructor_before_products {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (id : PrivateColumnId actions)
    (hindex : (privateColumnIndex id).val < 16 * actions) :
    plonkTotalColumnConstructor vk pub witness ch id =
      plonkTotalColumnConstructor vk pub witness ch' id := by
  cases id with
  | advice a c => rfl
  | lookupInput a l =>
    funext history
    simp only [plonkTotalColumnConstructor, plonkConstructColumnResult, htheta]
  | lookupTable a l =>
    funext history
    simp only [plonkTotalColumnConstructor, plonkConstructColumnResult, htheta]
  | permutationProduct a s =>
    have h := (privateColumnIndex_bounds (.permutationProduct a s)).1
    omega
  | lookupProduct a l =>
    have h := (privateColumnIndex_bounds (.lookupProduct a l)).1
    omega

/-- The complete advice and lookup-permutation schedule is independent of later challenges. -/
theorem plonkColumnSteps_take_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) :
    (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch)).take (16 * actions) =
      (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch')).take (16 * actions) := by
  simp only [plonkColumnSteps, ← List.map_take]
  apply List.map_congr_left
  intro id hid
  have hindex : (privateColumnIndex id).val < 16 * actions :=
    (List.mem_take_iff_idxOf_lt (privateColumnOrder_mem id)).mp hid
  rw [plonkTotalColumnConstructor_before_products vk pub witness ch ch' htheta id hindex]

/-- On every fixed row tape, the first `16m` computed columns depend only on `theta`. -/
theorem plonkTotalColumnRows_take_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (tape : Fin (126 * actions) → Fp) :
    (plonkTotalColumnRows vk pub witness ch tape).take (16 * actions) =
      (plonkTotalColumnRows vk pub witness ch' tape).take (16 * actions) := by
  apply columnRowsFromTape_take_congr
  · exact plonkColumnSteps_take_challenges vk pub witness ch ch' htheta
  · intro i j hij
    exact congrArg tape (Fin.ext hij)

/-- All pre-product column polynomials, not just their usable rows, ignore later challenges. -/
theorem plonkTotalColumnRows_polynomial_before_products {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (tape : Fin (126 * actions) → Fp)
    (id : PrivateColumnId actions) (hindex : (privateColumnIndex id).val < 16 * actions) :
    privateColumnPolynomial (plonkTotalColumnRows vk pub witness ch tape) id =
      privateColumnPolynomial (plonkTotalColumnRows vk pub witness ch' tape) id := by
  rw [← privateColumnPolynomial_take _ id (16 * actions) hindex,
    ← privateColumnPolynomial_take (plonkTotalColumnRows vk pub witness ch' tape) id (16 * actions) hindex,
    plonkTotalColumnRows_take_challenges vk pub witness ch ch' htheta tape]

/-- The actual packed permutation factor rows are also fixed before `beta` and `gamma`. -/
theorem plonkTotalColumnRows_permutation_factors {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (tape : Fin (126 * actions) → Fp) (a : Fin actions) :
    plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks =
      plonkPermutationFactorRows pub (plonkTotalColumnRows vk pub witness ch' tape) a vk.permutationChunks := by
  have hcut : 10 * actions ≤ 16 * actions := by omega
  rw [← plonkPermutationFactorRows_take _ _ (16 * actions) hcut,
    ← plonkPermutationFactorRows_take pub (plonkTotalColumnRows vk pub witness ch' tape)
      (16 * actions) hcut,
    plonkTotalColumnRows_take_challenges vk pub witness ch ch' htheta tape]

end Zcash.Snark.ZeroKnowledge
