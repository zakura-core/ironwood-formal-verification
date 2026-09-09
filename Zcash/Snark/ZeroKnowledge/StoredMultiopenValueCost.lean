import Zcash.Snark.ZeroKnowledge.StoredOpeningValueCost
import Zcash.Snark.ZeroKnowledge.ScalarHornerCost
import Zcash.Snark.ZeroKnowledge.OpeningEvaluationSetsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp URS)

/-- Compute the verifier's actual final claimed value from stored opening polynomials. -/
@[irreducible] def storedMultiopenValueCosted (costs : FieldOperationCosts) (read : ℕ)
    (x2 x4 point : Fp × ℕ) (groups : List StoredOpeningGroup) : Fp × ℕ :=
  let sets := mapListCosted (storedOpeningSetCosted costs read point) groups
  let quotient := multiopenEvalCosted costs read x2 point sets.1
  let values := mapListCosted (fun entry => (entry.2.2.1, read + 2)) sets.1
  let result := scalarHornerCosted read costs.add costs.multiply x4 (quotient.1 :: values.1)
  (result.1, sets.2 + quotient.2 + values.2 + result.2 + 2)

/-- Erasure preserves the exact interpolation, total divisions, and original final scalar fold. -/
theorem storedMultiopenValueCosted_result (costs : FieldOperationCosts) (read : ℕ)
    (x2 x4 point : Fp × ℕ) (groups : List StoredOpeningGroup) :
    (storedMultiopenValueCosted costs read x2 x4 point groups).1 =
      plonkScalarFold x4.1
        (multiopenEval x2.1 point.1 (groups.map fun group => group.erase.toPolynomialOpeningGroup.forVerifier point.1) ::
          groups.map (fun group => group.erase.polynomial.eval point.1)) := by
  unfold storedMultiopenValueCosted
  change (scalarHornerCosted read costs.add costs.multiply x4
    ((multiopenEvalCosted costs read x2 point (mapListCosted (storedOpeningSetCosted costs read point) groups).1).1 ::
      (mapListCosted (fun entry => (entry.2.2.1, read + 2))
        (mapListCosted (storedOpeningSetCosted costs read point) groups).1).1)).1 = _
  rewrite [scalarHornerCosted_result, multiopenEvalCosted_result]
  simp only [mapListCosted_result, List.map_map, Function.comp_def, storedOpeningSetCosted,
    densePolynomialNodeValuesCosted_result, listHornerCosted_densePolynomial_result,
    StoredOpeningGroup.erase, PolynomialOpeningGroup.forVerifier, PolynomialOpeningGroup.values]


/-- The source's computed scalar is this same fold without requiring distinct or excluded query points. -/
theorem computedMultiopenOpening_value_fold {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) (x2 x4 point qPrimeBlind : Fp) (groups : List BlindedOpeningGroup) :
    (computedMultiopenOpening urs x2 x4 point qPrimeBlind groups).2 =
      plonkScalarFold x4
        (multiopenEval x2 point (groups.map fun group => group.toPolynomialOpeningGroup.forVerifier point) ::
          groups.map (fun group => group.polynomial.eval point)) := by
  have hz : (groups.map (multiopenGroupMsm urs)).zip (groups.map fun group => group.polynomial.eval point) =
      groups.map (fun group => (multiopenGroupMsm urs group, group.polynomial.eval point)) := by
    induction groups with
    | nil => rfl
    | cons group groups ih => simp only [List.map_cons, List.zip_cons_cons, ih]
  simp only [computedMultiopenOpening, multiopenCombine_eq_pair, hz, plonkScalarFold,
    List.foldl_cons, zero_mul, zero_add, List.foldl_map]

/-- The actual stored calculation equals the original computed opening value on all inputs. -/
theorem storedMultiopenValueCosted_computed {G : Type*} [AddCommGroup G] [Module Fp G]
    (costs : FieldOperationCosts) (read : ℕ) (urs : URS G) (x2 x4 point : Fp × ℕ)
    (qPrimeBlind : Fp) (groups : List StoredOpeningGroup) :
    (storedMultiopenValueCosted costs read x2 x4 point groups).1 =
      (computedMultiopenOpening urs x2.1 x4.1 point.1 qPrimeBlind (groups.map StoredOpeningGroup.erase)).2 := by
  rewrite [storedMultiopenValueCosted_result, computedMultiopenOpening_value_fold]
  simp only [List.map_map, Function.comp_def]

end Zcash.Snark.ZeroKnowledge
