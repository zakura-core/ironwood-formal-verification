import Zcash.Snark.ZeroKnowledge.PartialExpressionMasking
import Zcash.Snark.ZeroKnowledge.PlonkMaskBoundary

/-!
# Boundary certificates that leave unrelated public values unknown

The finite checker visits the same gate and lookup boundaries as the full checker.
It needs agreement only at fixed queries for which a value is supplied. The partial
expression refinement then supplies the existing full mask profile.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Check the boundaries using only the declared known public fixed-query values. -/
def plonkPartialMaskBoundaryCheck {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (known : Fin 8 → ℕ → Option Fp) : Bool :=
  ((List.finRange 8).all fun row => vk.gates.all
    (exprPartialMaskInvariant (known row) (plonkAdviceQueryRetained (plonkMaskBoundaryRows row)))) &&
  ((List.finRange 2).all fun row => (List.finRange 3).all fun lookup =>
    (vk.lookupInputExprs lookup).all
      (exprPartialMaskInvariant (known (row.castLE (by decide)))
        (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide))))) &&
    (vk.lookupTableExprs lookup).all
      (exprPartialMaskInvariant (known (row.castLE (by decide)))
        (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide))))))

/-- Compatible public polynomials and a partial boundary certificate give the full mask profile. -/
theorem plonkPartialMaskBoundaryCheck_sound {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (known : Fin 8 → ℕ → Option Fp)
    (hagrees : ∀ boundary query value, known boundary query = some value →
      plonkFixedRowValues pub (plonkMaskBoundaryRows boundary) query = value)
    (hcheck : plonkPartialMaskBoundaryCheck vk known = true) : PlonkMaskingProfile vk pub := by
  simp only [plonkPartialMaskBoundaryCheck, Bool.and_eq_true] at hcheck
  apply plonkMaskingProfile_of_boundaries vk pub
  · intro boundary expr hexpr
    exact exprPartialMaskInvariant_refines _ _ (hagrees boundary) _ expr
      (List.all_eq_true.mp (List.all_eq_true.mp hcheck.1 boundary (List.mem_finRange boundary)) expr hexpr)
  · intro lookup boundary expr hexpr
    have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck.2 boundary
      (List.mem_finRange boundary)) lookup (List.mem_finRange lookup)
    simp only [Bool.and_eq_true] at h
    rw [← plonkMaskBoundaryRows_lookup boundary]
    exact exprPartialMaskInvariant_refines _ _ (hagrees _) _ expr (List.all_eq_true.mp h.1 expr hexpr)
  · intro lookup boundary expr hexpr
    have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck.2 boundary
      (List.mem_finRange boundary)) lookup (List.mem_finRange lookup)
    simp only [Bool.and_eq_true] at h
    rw [← plonkMaskBoundaryRows_lookup boundary]
    exact exprPartialMaskInvariant_refines _ _ (hagrees _) _ expr (List.all_eq_true.mp h.2 expr hexpr)

/-- Only these packed selector columns need known values at the initial row. -/
def plonkInitialMaskColumns : List ℕ := [18, 20, 21, 24]

/-- Every initial mask-check column belongs to the packed-selector suffix of the captured layout. -/
theorem plonkInitialMaskColumns_bounds (query : ℕ) (hquery : query ∈ plonkInitialMaskColumns) :
    14 ≤ query ∧ query < 29 := by
  simp [plonkInitialMaskColumns] at hquery
  rcases hquery with rfl | rfl | rfl | rfl <;> decide

/-- Four selectors are zero at row 0; all packed selectors are zero at the later boundaries. -/
def plonkSelectorBoundaryKnown (boundary : Fin 8) (query : ℕ) : Option Fp :=
  if boundary.val = 0 then
    if query ∈ plonkInitialMaskColumns then some 0 else none
  else if query < 14 then none else some 0

end Zcash.Snark.ZeroKnowledge
