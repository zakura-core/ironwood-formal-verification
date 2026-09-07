import Zcash.Snark.ZeroKnowledge.PlonkPrefix
import Zcash.Snark.ZeroKnowledge.PlonkQuotientSimulation

/-!
# Challenge dependencies of the reference columns and quotient

On a fixed replacement-row tape, advice columns precede every verifier
challenge. All columns use only `theta,beta,gamma`; the quotient additionally
uses `y`. Earlier results give the intermediate lookup-permutation prefix's
dependence on `theta` alone. These pointwise properties include the totalized
fallbacks and require no valid-witness or nonzero-challenge assumptions.

The complete tape decoder and staged commitments still need to be connected
to these column facts for the full reference-prover causality theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Every column constructor is fixed once the three product-stage challenges are fixed. -/
theorem plonkTotalColumnConstructor_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma) :
    plonkTotalColumnConstructor vk pub witness left = plonkTotalColumnConstructor vk pub witness right := by
  funext id history
  simp only [plonkTotalColumnConstructor,
    plonkConstructColumnResult_challenges vk pub witness left right htheta hbeta hgamma]

/-- Constructors in the initial advice block do not inspect any verifier challenge. -/
theorem plonkTotalColumnConstructor_before_theta {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (id : PrivateColumnId actions) (hindex : (privateColumnIndex id).val < 10 * actions) :
    plonkTotalColumnConstructor vk pub witness left id =
      plonkTotalColumnConstructor vk pub witness right id := by
  cases id with
  | advice a c => rfl
  | lookupInput a l => have h := (privateColumnIndex_bounds (.lookupInput a l)).1; omega
  | lookupTable a l => have h := (privateColumnIndex_bounds (.lookupTable a l)).1; omega
  | permutationProduct a s => have h := (privateColumnIndex_bounds (.permutationProduct a s)).1; omega
  | lookupProduct a l => have h := (privateColumnIndex_bounds (.lookupProduct a l)).1; omega

/-- The entire initial advice schedule is fixed before `theta`. -/
theorem plonkColumnSteps_take_before_theta {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp) :
    (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness left)).take (10 * actions) =
      (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness right)).take (10 * actions) := by
  simp only [plonkColumnSteps, ← List.map_take]
  apply List.map_congr_left
  intro id hid
  have hindex : (privateColumnIndex id).val < 10 * actions :=
    (List.mem_take_iff_idxOf_lt (privateColumnOrder_mem id)).mp hid
  rw [plonkTotalColumnConstructor_before_theta vk pub witness left right id hindex]

/-- The first `10m` masked column polynomials use only their fixed private tape and witness. -/
theorem plonkTotalColumnRows_take_before_theta {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    (plonkTotalColumnRows vk pub witness left tape).take (10 * actions) =
      (plonkTotalColumnRows vk pub witness right tape).take (10 * actions) := by
  apply columnRowsFromTape_take_congr
  · exact plonkColumnSteps_take_before_theta vk pub witness left right
  · intro i j hij
    exact congrArg tape (Fin.ext hij)

/-- In particular, every initial advice polynomial is independent of the whole verifier tape. -/
theorem plonkTotalColumnRows_advice_before_theta {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) (c : Fin 10) :
    privateColumnPolynomial (plonkTotalColumnRows vk pub witness left tape) (.advice a c) =
      privateColumnPolynomial (plonkTotalColumnRows vk pub witness right tape) (.advice a c) := by
  have hindex := privateColumnIndex_bounds (.advice a c)
  rw [← privateColumnPolynomial_take _ (.advice a c) (10 * actions) hindex,
    ← privateColumnPolynomial_take (plonkTotalColumnRows vk pub witness right tape)
      (.advice a c) (10 * actions) hindex,
    plonkTotalColumnRows_take_before_theta vk pub witness left right tape]

/-- Complete masked row states cannot depend on challenges after `theta,beta,gamma`. -/
theorem plonkTotalColumnRows_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (tape : Fin (126 * actions) → Fp) :
    plonkTotalColumnRows vk pub witness left tape = plonkTotalColumnRows vk pub witness right tape := by
  apply columnRowsFromTape_cast_eq
  rw [plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma]

/-- The symbolic constraint model also ignores later evaluation and opening challenges. -/
theorem plonkConstraintModel_challenges {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Challenges k Fp) (rows : ColumnHistory 2048)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma) :
    plonkConstraintModel vk pub left rows = plonkConstraintModel vk pub right rows := by
  simp only [plonkConstraintModel, htheta, hbeta, hgamma]

/-- The eight computed quotient pieces need `y` and the earlier three challenges, but never `x`. -/
theorem plonkHonestQuotientPieces_challenges {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Challenges k Fp) (rows : ColumnHistory 2048)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) :
    plonkHonestQuotientPieces vk pub left rows = plonkHonestQuotientPieces vk pub right rows := by
  simp only [plonkHonestQuotientPieces, plonkConstraintNumerator_eq_fold,
    plonkConstraintModel_challenges vk pub left right rows htheta hbeta hgamma, hy]

end Zcash.Snark.ZeroKnowledge
