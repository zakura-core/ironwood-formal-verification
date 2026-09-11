import Zcash.Snark.ZeroKnowledge.DenseQuotientPieces

/-!
# Iterative quotient division for prover replay

Constraint numerators exceed the interpreter's stack capacity for the reference
synthetic-division recursion. Tail-recursive folds compute the same coefficient
lists, retaining their padding, root order, and remainders. The equalities below
connect the folds to the existing dense division on every input.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp)
open Zcash.Snark.ZeroKnowledge

/-- Scan coefficients from highest to lowest degree with a tail-recursive fold. -/
def syntheticDivision (root : Fp) (values : List Fp) : List Fp × Fp :=
  values.reverse.foldl
    (fun upper first => (upper.2 :: upper.1, first + root * upper.2)) ([], 0)

/-- The iterative scan retains every quotient coefficient and the original remainder. -/
theorem syntheticDivision_result (root : Fp) (values : List Fp) :
    syntheticDivision root values = (denseSyntheticCosted 0 0 0 root values).1 := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    unfold syntheticDivision at ih ⊢
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      denseSyntheticCosted]
    rw [ih]

/-- Divide by the supplied roots in order, retaining the padded coefficient width. -/
def divideRoots (roots values : List Fp) : List Fp :=
  roots.foldl (fun current root => (syntheticDivision root current).1) values

/-- The iterative root loop returns the exact coefficient list of the reference division. -/
theorem divideRoots_result (roots values : List Fp) :
    divideRoots roots values = (denseDivRootsCosted 0 0 0 roots values).1 := by
  induction roots generalizing values with
  | nil => rfl
  | cons root rest ih =>
    change divideRoots rest (syntheticDivision root values).1 = _
    rw [syntheticDivision_result, ih]
    rfl

/-- Use the original domain-root enumeration with iterative coefficient scans. -/
def divideDomain (k : ℕ) (values : List Fp) : List Fp :=
  divideRoots (domainRootsCosted 0 0 k).1 values

/-- Iterative division agrees on all inputs, without an exact-divisibility premise. -/
theorem divideDomain_result (k : ℕ) (values : List Fp) :
    divideDomain k values = (denseDomainQuotientCosted 0 0 0 0 k values).1 := by
  unfold divideDomain denseDomainQuotientCosted
  exact divideRoots_result _ _

/-- Cache coefficients before reading the consecutive, zero-padded blocks. -/
def coefficientBlocks (size count : ℕ) (values : List Fp) : List (List Fp) :=
  let stored := values.toArray
  List.ofFn fun block : Fin count =>
    List.ofFn fun index : Fin size => (stored[size * block.val + index.val]?).getD 0

/-- Array reads preserve every coefficient, including out-of-range zero padding. -/
theorem coefficientBlocks_result (size count : ℕ) (values : List Fp) :
    coefficientBlocks size count values = (denseCoefficientBlocksCosted 0 size count values).1 := by
  simp only [coefficientBlocks, denseCoefficientBlocksCosted, ofFnCosted_result,
    denseCoefficientBlockCosted, getDListCosted_result, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-- Materialize the original eight quotient pieces after dividing the complete numerator. -/
def splitQuotient (values : List Fp) : List (List Fp) :=
  coefficientBlocks 2048 8 (divideDomain 11 values)

/-- Every padded coefficient and piece boundary agrees with the existing quotient constructor. -/
theorem splitQuotient_result (values : List Fp) :
    splitQuotient values = (densePlonkQuotientPiecesCosted 0 0 0 0 values).1 := by
  unfold splitQuotient densePlonkQuotientPiecesCosted denseDomainPiecesCosted
  rw [coefficientBlocks_result, divideDomain_result]

end Zcash.Snark.Fixtures.Prover
