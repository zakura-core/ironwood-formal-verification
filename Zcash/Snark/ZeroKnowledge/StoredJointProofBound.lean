import Zcash.Snark.ZeroKnowledge.StoredJointProofCost
import Zcash.Snark.ZeroKnowledge.RoutedProofBound

/-! # Complete proof-reader and preparation bounds from stored joint data -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)

/-- Public interpolation and every stored-list reader fit this explicit common input price. -/
def storedJointProofInputBudget (costs : FieldOperationCosts)
    (read omegaAccess rowRead xAccess points rounds : ℕ) : ℕ :=
  publicRowEvaluationCostBudget costs rowRead omegaAccess xAccess + 2 * points + 2 * rounds + read + 13

/-- The actual stored inputs discharge every complete proof-field reader premise. -/
theorem storedJointProofCosted_readBound (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G)
    (rowRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hrows : ∀ row ∈ joint.1.2.1, row.length ≤ 5) :
    ProofFieldReadBound (storedJointProofCosted (k := k) costs equal read omegaAccess
      instances fixed sigma x x1 joint).1
      (routedProofReadBudget actions joint.1.2.1.length equal read
        (storedJointProofInputBudget costs read omegaAccess rowRead x.2
          joint.1.1.length joint.2.messages.length)) := by
  let access := storedJointProofInputBudget costs read omegaAccess rowRead x.2
    joint.1.1.length joint.2.messages.length
  have hpublic (rows : Fin 2048 → Fp × ℕ) (hread : ∀ row, (rows row).2 ≤ rowRead) :
      (rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) rows x).2 ≤ access := by
    have h := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess) rows x rowRead hread
    change _ ≤ publicRowEvaluationCostBudget costs rowRead omegaAccess x.2 at h
    exact h.trans (by dsimp only [access, storedJointProofInputBudget]; omega)
  have hsmall : read + 11 ≤ access := by
    dsimp only [access, storedJointProofInputBudget]
    omega
  have hipa := storedIpaReadersCosted_readBound (k := k) read joint.2
  have htail : 2 * joint.2.messages.length + read + 3 ≤ access := by
    dsimp only [access, storedJointProofInputBudget]
    omega
  change ProofFieldReadBound _ (routedProofReadBudget actions joint.1.2.1.length equal read access)
  rw [← storedRowReadersCosted_length read (0 : Fp) 5 joint.1.2.1]
  apply plonkRoutedProofCosts_readBound (access := access)
  · intro action
    exact hpublic _ (hinstances action)
  · intro column
    exact hpublic _ (hfixed column)
  · intro column
    exact hpublic _ (hsigma column)
  · intro column hcolumn index
    have h := storedRowReadersCosted_readBound read (0 : Fp) 5 joint.1.2.1 5 hrows column hcolumn index
    omega
  · intro index
    have h := getDListCosted_cost_le read (0 : G) joint.1.1 index.val
    dsimp only [access, storedJointProofInputBudget]
    exact h.trans (by omega)
  · exact (by omega : read + 1 ≤ access)
  · intro index
    have h := getDListCosted_cost_le read (0 : Fp)
      (openingGroupValuesCosted (actions := actions) costs equal read
        (storedRowReadersCosted read (0 : Fp) 5 joint.1.2.1).1 x1 (joint.1.2.2.2, read + 1)).1 index.val
    rw [openingGroupValuesCosted_length] at h
    omega
  · exact hipa.1.trans htail
  · intro round
    exact ⟨((hipa.2.1 round).1).trans htail, ((hipa.2.1 round).2).trans htail⟩
  · exact hipa.2.2.1.trans htail
  · exact hipa.2.2.2.trans htail

/-- The adapter pays for all observation-reader preparation and all five group-value producers. -/
theorem storedJointProofCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G)
    (hrows : ∀ row ∈ joint.1.2.1, row.length ≤ 5) :
    (storedJointProofCosted (k := k) costs equal read omegaAccess instances fixed sigma x x1 joint).2 ≤
      3 * joint.1.2.1.length + read +
        4 * (privateOpeningEvaluationCostBudget costs equal read actions joint.1.2.1.length (read + 11) x1.2 + 1) + 65 := by
  let views := storedRowReadersCosted read (0 : Fp) 5 joint.1.2.1
  have hv := storedRowReadersCosted_cost_le read (0 : Fp) 5 joint.1.2.1
  have hviews : ∀ column ∈ views.1, ∀ index, (column index).2 ≤ read + 11 := by
    intro column hcolumn index
    have h := storedRowReadersCosted_readBound read (0 : Fp) 5 joint.1.2.1 5 hrows column hcolumn index
    omega
  have hg := openingGroupValuesCosted_cost_le (actions := actions) costs equal read views.1 x1
    (joint.1.2.2.2, read + 1) (read + 11) hviews
  have hlength : views.1.length = joint.1.2.1.length := storedRowReadersCosted_length _ _ _ _
  rw [hlength] at hg
  change views.2 + (openingGroupValuesCosted (actions := actions) costs equal read views.1 x1
    (joint.1.2.2.2, read + 1)).2 + 40 ≤ _
  change views.2 ≤ _ at hv
  dsimp only at hg
  omega

end Zcash.Snark.ZeroKnowledge
