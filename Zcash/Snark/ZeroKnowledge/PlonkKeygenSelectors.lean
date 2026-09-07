import Zcash.Snark.ZeroKnowledge.KeygenSelectorSupport
import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed
import Zcash.Snark.ZeroKnowledge.PlonkSelectorCertificate

/-!
# Compiler selector support reduces mask safety to its initial row

When the original fixed-column prefix ends by column 14 and V1 placement ends by
row 2041, the compiler supplies zero for every packed selector at all later mask
boundaries. Only four initial packed-selector zeros remain to be established from
the concrete circuit. Zero padding covers indices outside the compiler's column
and row ranges, so this profile needs no compiler-domain or fixed-column-count
premise. The certificates impose no conditions on the other fixed values,
including the table fill in row 2041.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Packed selector columns retain their column indices in the fixed-query order. -/
theorem plonkFixedQueryOrder_selector (query : Fin 29) (hquery : 14 ≤ query.val) :
    plonkFixedQueryOrder query = query := by
  fin_cases query <;> simp [plonkFixedQueryOrder] at *

/-- Every noninitial mask boundary is at or after row 2041. -/
theorem plonkMaskBoundaryRows_after_zero (boundary : Fin 8) (hboundary : boundary.val ≠ 0) :
    2041 ≤ (plonkMaskBoundaryRows boundary).val := by
  fin_cases boundary <;> simp [plonkMaskBoundaryRows] at *

/-- The compiler's placement bound forces all noninitial packed-selector boundaries to zero. -/
theorem plonkKeygenFixedRows_selector_zero (top : TopLevelCircuit Fp Config PublicInput)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (column : Fin 29) (hcolumn : 14 ≤ column.val)
    (row : Fin 2048) (hrow : 2041 ≤ row.val) :
    plonkKeygenFixedRows top column row = 0 := by
  exact topLevelSelectorRows_zero_after_placement top column.val row.val
    (hprefix.trans hcolumn) (hplacement.trans hrow)

/-- The initial selector row and compiler support give every known public boundary value. -/
theorem plonkKeygenPublicPolynomials_selectorBoundary_agrees {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (boundary : Fin 8) (query : ℕ) (value : Fp)
    (hknown : plonkSelectorBoundaryKnown boundary query = some value) :
    plonkFixedRowValues (plonkKeygenPublicPolynomials top instances sigma)
      (plonkMaskBoundaryRows boundary) query = value := by
  rw [plonkKeygenPublicPolynomials, plonkPublicPolynomialsFromRows_fixedRowValues]
  by_cases hboundary : boundary.val = 0
  · have hzero : boundary = 0 := Fin.ext hboundary
    subst boundary
    by_cases hmember : query ∈ plonkInitialMaskColumns
    · obtain ⟨hselector, hquery⟩ := plonkInitialMaskColumns_bounds query hmember
      have hvalue : (0 : Fp) = value := by
        simpa [plonkSelectorBoundaryKnown, hmember] using hknown
      simpa only [finFn, hquery, ↓reduceDIte,
        plonkFixedQueryOrder_selector ⟨query, hquery⟩ hselector, plonkMaskBoundaryRows] using
          (hfirst ⟨query, hquery⟩ hmember).trans hvalue
    · simp [plonkSelectorBoundaryKnown, hmember] at hknown
  · by_cases hsmall : query < 14
    · simp [plonkSelectorBoundaryKnown, hboundary, hsmall] at hknown
    have hvalue : (0 : Fp) = value := by
      simpa [plonkSelectorBoundaryKnown, hboundary, hsmall] using hknown
    by_cases hquery : query < 29
    · have hselector : 14 ≤ query := Nat.le_of_not_gt hsmall
      simp only [finFn, hquery, ↓reduceDIte]
      rw [plonkFixedQueryOrder_selector ⟨query, hquery⟩ hselector]
      exact (plonkKeygenFixedRows_selector_zero top hprefix hplacement
        ⟨query, hquery⟩ hselector (plonkMaskBoundaryRows boundary)
        (plonkMaskBoundaryRows_after_zero boundary hboundary)).trans hvalue
    · simpa [finFn, hquery] using hvalue

/-- The public selector certificate and the compiler's initial selector row supply mask safety. -/
theorem plonkKeygenPublicPolynomials_selectorMaskingProfile {actions k : ℕ} {G : Type*}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true) :
    PlonkMaskingProfile vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkPartialMaskBoundaryCheck_sound vk _ _
    (plonkKeygenPublicPolynomials_selectorBoundary_agrees top hprefix hplacement hfirst instances sigma)
    hcheck

/-- The one-Action captured key is mask-safe for compiler fixed rows with the stated initial selectors. -/
theorem singleAction_plonkKeygenSelectorProfile
    (top : TopLevelCircuit Fp Config PublicInput)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (instances : Fin 1 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkMaskingProfile (k := 11) Fixture.vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkKeygenPublicPolynomials_selectorMaskingProfile top hprefix hplacement hfirst
    instances sigma Fixture.vk singleAction_plonkSelectorBoundary

/-- The two-Action captured key has the same compiler-selector mask profile. -/
theorem multiAction_plonkKeygenSelectorProfile
    (top : TopLevelCircuit Fp Config PublicInput)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (instances : Fin 2 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkMaskingProfile (k := 11) Fixture2.vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkKeygenPublicPolynomials_selectorMaskingProfile top hprefix hplacement hfirst
    instances sigma Fixture2.vk multiAction_plonkSelectorBoundary

end Zcash.Snark.ZeroKnowledge
