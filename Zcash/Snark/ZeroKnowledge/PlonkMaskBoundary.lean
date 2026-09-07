import Zcash.Snark.ZeroKnowledge.PlonkOriginalRows

/-!
# Public mask safety reduces to eight boundary rows

Every current/next/previous advice query at rows 1 through 2040 targets a retained
row. Gates therefore need explicit selector checks only at row 0 and rows 2041 through
2047; lookups need only rows 0 and 2041. The finite checker accepts fixed-query row
values, and a separate equality ties those values to the public polynomials.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The only domain rows at which some advice query can read a replaced cell. -/
def plonkMaskBoundaryRows : Fin 8 → Fin 2048 := ![0, 2041, 2042, 2043, 2044, 2045, 2046, 2047]

/-- The two boundary rows that also belong to the usable lookup prefix. -/
def plonkLookupMaskBoundaryRows : Fin 2 → Fin 2042 := ![0, 2041]

/-- The lookup boundaries are the first two entries of the full boundary list. -/
theorem plonkMaskBoundaryRows_lookup (row : Fin 2) :
    plonkMaskBoundaryRows (row.castLE (by decide)) =
      (plonkLookupMaskBoundaryRows row).castLE (by decide) := by
  fin_cases row <;> rfl

/-- Every advice query is retained in the interior, including out-of-range zero queries. -/
theorem plonkAdviceQueryRetained_interior (row : Fin 2048) (hlo : 0 < row.val) (hhi : row.val < 2041)
    (query : ℕ) : plonkAdviceQueryRetained row query = true := by
  have hrotation (rotation : Fin 3) : (plonkAdviceRotationRow rotation row).val < 2042 := by
    fin_cases rotation <;> simp [plonkAdviceRotationRow, plonkAdviceRotationOffsets] <;> omega
  unfold plonkAdviceQueryRetained
  split
  · exact decide_eq_true (hrotation _)
  · rfl

/-- Interior expressions pass the public checker for every fixed-column valuation. -/
theorem plonkExpressionMaskCheck_interior {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (row : Fin 2048) (hlo : 0 < row.val) (hhi : row.val < 2041) (expr : Expr Fp) :
    plonkExpressionMaskCheck pub row expr = true :=
  exprMaskInvariant_of_retained_all _ _ (plonkAdviceQueryRetained_interior row hlo hhi) expr

private theorem boundaryRow_exists (row : Fin 2048) (h : ¬ (0 < row.val ∧ row.val < 2041)) :
    ∃ boundary, plonkMaskBoundaryRows boundary = row := by
  rcases row with ⟨row, hrow⟩
  have hcases : row = 0 ∨ row = 2041 ∨ row = 2042 ∨ row = 2043 ∨ row = 2044 ∨ row = 2045 ∨ row = 2046 ∨ row = 2047 := by
    change ¬ (0 < row ∧ row < 2041) at h
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;> subst row
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

private theorem lookupBoundaryRow_exists (row : Fin 2042) (h : ¬ (0 < row.val ∧ row.val < 2041)) :
    ∃ boundary, plonkLookupMaskBoundaryRows boundary = row := by
  rcases row with ⟨row, hrow⟩
  have hcases : row = 0 ∨ row = 2041 := by
    change ¬ (0 < row ∧ row < 2041) at h
    omega
  rcases hcases with h | h <;> subst row
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- The public profile follows from gate and lookup checks at the finite boundary rows. -/
theorem plonkMaskingProfile_of_boundaries {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (hgates : ∀ boundary : Fin 8, ∀ expr ∈ vk.gates,
      plonkExpressionMaskCheck pub (plonkMaskBoundaryRows boundary) expr = true)
    (hinputs : ∀ lookup : Fin 3, ∀ boundary : Fin 2, ∀ expr ∈ vk.lookupInputExprs lookup,
      plonkExpressionMaskCheck pub ((plonkLookupMaskBoundaryRows boundary).castLE (by decide)) expr = true)
    (htables : ∀ lookup : Fin 3, ∀ boundary : Fin 2, ∀ expr ∈ vk.lookupTableExprs lookup,
      plonkExpressionMaskCheck pub ((plonkLookupMaskBoundaryRows boundary).castLE (by decide)) expr = true) :
    PlonkMaskingProfile vk pub := by
  constructor
  · intro row expr hexpr
    by_cases h : 0 < row.val ∧ row.val < 2041
    · exact plonkExpressionMaskCheck_interior pub row h.1 h.2 expr
    · obtain ⟨boundary, rfl⟩ := boundaryRow_exists row h
      exact hgates boundary expr hexpr
  · intro lookup row expr hexpr
    by_cases h : 0 < row.val ∧ row.val < 2041
    · exact plonkExpressionMaskCheck_interior pub (row.castLE (by decide)) h.1 h.2 expr
    · obtain ⟨boundary, rfl⟩ := lookupBoundaryRow_exists row h
      exact hinputs lookup boundary expr hexpr
  · intro lookup row expr hexpr
    by_cases h : 0 < row.val ∧ row.val < 2041
    · exact plonkExpressionMaskCheck_interior pub (row.castLE (by decide)) h.1 h.2 expr
    · obtain ⟨boundary, rfl⟩ := lookupBoundaryRow_exists row h
      exact htables lookup boundary expr hexpr

/-- Check every gate and lookup boundary using supplied fixed-query values only. -/
def plonkMaskBoundaryCheck {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (fixed : Fin 8 → ℕ → Fp) : Bool :=
  ((List.finRange 8).all fun row => vk.gates.all
    (exprMaskInvariant (fixed row) (plonkAdviceQueryRetained (plonkMaskBoundaryRows row)))) &&
  ((List.finRange 2).all fun row => (List.finRange 3).all fun lookup =>
    (vk.lookupInputExprs lookup).all
      (exprMaskInvariant (fixed (row.castLE (by decide)))
        (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide))))) &&
    (vk.lookupTableExprs lookup).all
      (exprMaskInvariant (fixed (row.castLE (by decide)))
        (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide))))))

/-- Passing the boundary checker supplies the full mask profile when the public row values agree. -/
theorem plonkMaskBoundaryCheck_sound {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (fixed : Fin 8 → ℕ → Fp)
    (hfixed : ∀ row, plonkFixedRowValues pub (plonkMaskBoundaryRows row) = fixed row)
    (hcheck : plonkMaskBoundaryCheck vk fixed = true) : PlonkMaskingProfile vk pub := by
  simp only [plonkMaskBoundaryCheck, Bool.and_eq_true] at hcheck
  apply plonkMaskingProfile_of_boundaries vk pub
  · intro row expr hexpr
    change exprMaskInvariant (plonkFixedRowValues pub (plonkMaskBoundaryRows row))
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows row)) expr = true
    rw [hfixed row]
    exact List.all_eq_true.mp (List.all_eq_true.mp hcheck.1 row (List.mem_finRange row)) expr hexpr
  · intro lookup row expr hexpr
    have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck.2 row (List.mem_finRange row)) lookup (List.mem_finRange lookup)
    simp only [Bool.and_eq_true] at h
    rw [← plonkMaskBoundaryRows_lookup row]
    change exprMaskInvariant (plonkFixedRowValues pub (plonkMaskBoundaryRows (row.castLE (by decide))))
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide)))) expr = true
    rw [hfixed]
    exact List.all_eq_true.mp h.1 expr hexpr
  · intro lookup row expr hexpr
    have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck.2 row (List.mem_finRange row)) lookup (List.mem_finRange lookup)
    simp only [Bool.and_eq_true] at h
    rw [← plonkMaskBoundaryRows_lookup row]
    change exprMaskInvariant (plonkFixedRowValues pub (plonkMaskBoundaryRows (row.castLE (by decide))))
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows (row.castLE (by decide)))) expr = true
    rw [hfixed]
    exact List.all_eq_true.mp h.2 expr hexpr

end Zcash.Snark.ZeroKnowledge
