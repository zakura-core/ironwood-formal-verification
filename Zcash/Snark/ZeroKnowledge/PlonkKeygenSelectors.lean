import Zcash.Snark.ZeroKnowledge.KeygenSelectorSupport
import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed
import Zcash.Snark.ZeroKnowledge.PlonkSelectorCertificate

/-!
# Compiler selector support reduces mask safety to its initial row

When the original fixed-column prefix ends by column 13 and V1 placement ends by
row 2041, the compiler supplies zero for every packed selector at all later mask
boundaries. Only the initial packed-selector values remain to be established from
the concrete circuit. The certificates impose no conditions on the other fixed
values, including the table fill in row 2041.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Packed selector columns retain their column indices in the fixed-query order. -/
theorem plonkFixedQueryOrder_selector (query : Fin 29) (hquery : 13 ≤ query.val) :
    plonkFixedQueryOrder query = query := by
  fin_cases query <;> simp [plonkFixedQueryOrder] at *

/-- Every noninitial mask boundary is at or after row 2041. -/
theorem plonkMaskBoundaryRows_after_zero (boundary : Fin 8) (hboundary : boundary.val ≠ 0) :
    2041 ≤ (plonkMaskBoundaryRows boundary).val := by
  fin_cases boundary <;> simp [plonkMaskBoundaryRows] at *

/-- The compiler's placement bound forces all noninitial packed-selector boundaries to zero. -/
theorem plonkKeygenFixedRows_selector_zero (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 13)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (column : Fin 29) (hcolumn : 13 ≤ column.val)
    (row : Fin 2048) (hrow : 2041 ≤ row.val) :
    plonkKeygenFixedRows top column row = 0 := by
  exact topLevelSelectorRows_zero_of_placementEnd_le top column.val row.val
    (hprefix.trans hcolumn) (column.isLt.trans_le hcolumns)
    (by simpa only [TopLevelCircuit.n, hk] using row.isLt) (hplacement.trans hrow)

/-- The initial selector row and compiler support give every known public boundary value. -/
theorem plonkKeygenPublicPolynomials_selectorBoundary_agrees {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 13)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, 13 ≤ column.val →
      plonkKeygenFixedRows top column 0 = if column.val = 19 then 4 else 0)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (boundary : Fin 8) (query : ℕ) (value : Fp)
    (hknown : plonkSelectorBoundaryKnown boundary query = some value) :
    plonkFixedRowValues (plonkKeygenPublicPolynomials top instances sigma)
      (plonkMaskBoundaryRows boundary) query = value := by
  by_cases hsmall : query < 13
  · simp [plonkSelectorBoundaryKnown, hsmall] at hknown
  have hvalue : (if boundary.val = 0 ∧ query = 19 then (4 : Fp) else 0) = value := by
    simpa only [plonkSelectorBoundaryKnown, if_neg hsmall, Option.some.injEq] using hknown
  rw [← hvalue, plonkKeygenPublicPolynomials, plonkPublicPolynomialsFromRows_fixedRowValues]
  by_cases hquery : query < 29
  · have hselector : 13 ≤ query := Nat.le_of_not_gt hsmall
    simp only [finFn, hquery, ↓reduceDIte]
    rw [plonkFixedQueryOrder_selector ⟨query, hquery⟩ hselector]
    by_cases hboundary : boundary.val = 0
    · have hzero : boundary = 0 := Fin.ext hboundary
      subst boundary
      simpa only [Fin.val_zero, true_and, plonkMaskBoundaryRows] using hfirst ⟨query, hquery⟩ hselector
    · simpa only [hboundary, false_and, ite_false] using
        plonkKeygenFixedRows_selector_zero top hk hcolumns hprefix hplacement
          ⟨query, hquery⟩ hselector (plonkMaskBoundaryRows boundary)
          (plonkMaskBoundaryRows_after_zero boundary hboundary)
  · have hneq : query ≠ 19 := by omega
    simp [finFn, hquery, hneq]

/-- The public selector certificate and the compiler's initial selector row supply mask safety. -/
theorem plonkKeygenPublicPolynomials_selectorMaskingProfile {actions k : ℕ} {G : Type*}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 13)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, 13 ≤ column.val →
      plonkKeygenFixedRows top column 0 = if column.val = 19 then 4 else 0)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true) :
    PlonkMaskingProfile vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkPartialMaskBoundaryCheck_sound vk _ _
    (plonkKeygenPublicPolynomials_selectorBoundary_agrees top hk hcolumns hprefix hplacement hfirst instances sigma)
    hcheck

/-- The one-Action captured key is mask-safe for compiler fixed rows with the stated initial selectors. -/
theorem singleAction_plonkKeygenSelectorProfile
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 13)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, 13 ≤ column.val →
      plonkKeygenFixedRows top column 0 = if column.val = 19 then 4 else 0)
    (instances : Fin 1 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkMaskingProfile (k := 11) Fixture.vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkKeygenPublicPolynomials_selectorMaskingProfile top hk hcolumns hprefix hplacement hfirst
    instances sigma Fixture.vk singleAction_plonkSelectorBoundary

/-- The two-Action captured key has the same compiler-selector mask profile. -/
theorem multiAction_plonkKeygenSelectorProfile
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 13)
    (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, 13 ≤ column.val →
      plonkKeygenFixedRows top column 0 = if column.val = 19 then 4 else 0)
    (instances : Fin 2 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkMaskingProfile (k := 11) Fixture2.vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkKeygenPublicPolynomials_selectorMaskingProfile top hk hcolumns hprefix hplacement hfirst
    instances sigma Fixture2.vk multiAction_plonkSelectorBoundary

end Zcash.Snark.ZeroKnowledge
