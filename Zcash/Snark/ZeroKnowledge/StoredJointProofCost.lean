import Zcash.Snark.ZeroKnowledge.RoutedProofCost
import Zcash.Snark.ZeroKnowledge.StoredIpaReadCost
import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCost
import Zcash.Snark.ZeroKnowledge.OpeningScalarVectorsCost

/-!
# Routing the fully stored joint simulation into the original proof

The adapter constructs readers for the stored private observations, computes all
five group values, and supplies complete public polynomial producers and IPA
readers. Its preparation cost remains separate from the costs of forcing the
proof fields while constructing the transcript.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)

/-- Produce the priced proof from the complete materialized PLONK and IPA view. -/
def storedJointProofCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) :
    ProofString (plonkProofShape actions k) (Fp × ℕ) (G × ℕ) × ℕ :=
  let mask := joint.1
  let views := storedRowReadersCosted read (0 : Fp) 5 mask.2.1
  let points := fun index : Fin (22 * actions + 10) => getDListCosted read (0 : G) mask.1 index.val
  let groups := openingGroupValuesCosted (actions := actions) costs equal read views.1 x1 (mask.2.2.2, read + 1)
  let tail := storedIpaReadersCosted (k := k) read joint.2
  (plonkRoutedProofCosts equal read
    (fun action => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (instances action) x)
    (fun column => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (fixed column) x)
    (fun column => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (sigma column) x)
    views.1 points (mask.2.2.1, read + 1)
    (fun index : Fin 5 => getDListCosted read (0 : Fp) groups.1 index.val) tail,
   views.2 + groups.2 + 40)

set_option maxRecDepth 10000 in
/-- The stored adapter recovers the original full proof for every joint view and challenge value. -/
theorem storedJointProofCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G]
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (x x1 : Fp × ℕ)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    eraseProofCosts (storedJointProofCosted costs equal read omegaAccess instances fixed sigma x x1
      (materializePlonkJointView view)).1 =
      plonkProofFromJointView
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 x1.1 view := by
  let pub := plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
    (fun column row => (fixed column row).1) (fun column row => (sigma column row).1)
  let mask := materializePlonkMaskView view.1
  let views := storedRowReadersCosted read (0 : Fp) 5 mask.2.1
  let points := fun index : Fin (22 * actions + 10) => getDListCosted read (0 : G) mask.1 index.val
  let groups := openingGroupValuesCosted (actions := actions) costs equal read views.1 x1 (mask.2.2.2, read + 1)
  have hpoints : (fun index => (points index).1) = view.1.1 := by
    funext index
    exact getDListCosted_ofFn_result read 0 view.1.1 index
  have hviews : views.1.map (fun column index => (column index).1) = view.1.2.1 :=
    storedRowReadersCosted_erase_materialize read 0 view.1.2.1
  have hgroups : groups.1 = List.ofFn (plonkPreIpaProjection pub x.1 x1.1 view.1).groupValues := by
    have h := openingGroupValuesCosted_result costs equal read views.1 x1 (mask.2.2.2, read + 1)
      pub x.1 view.1.2.2.1 view.1.1
    rw [hviews] at h
    exact h
  have hgroupReaders : (fun index : Fin 5 =>
      (getDListCosted read (0 : Fp) groups.1 index.val).1) =
        (plonkPreIpaProjection pub x.1 x1.1 view.1).groupValues := by
    rw [hgroups]
    exact funext fun index => getDListCosted_ofFn_result read 0 _ index
  change eraseProofCosts (plonkRoutedProofCosts equal read
    (fun action => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (instances action) x)
    (fun column => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (fixed column) x)
    (fun column => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (sigma column) x)
    views.1 points (mask.2.2.1, read + 1)
    (fun index : Fin 5 => getDListCosted read (0 : Fp) groups.1 index.val)
    (storedIpaReadersCosted read (materializedIpaTranscript view.2))) = _
  rw [plonkRoutedProofCosts_result]
  change plonkProofString _ _ _ _ _ _ _
    (storedIpaReadersCosted read (materializedIpaTranscript view.2)).eraseCosts = _
  rw [hpoints, hviews, hgroupReaders, storedIpaReadersCosted_result]
  simp only [rowPolynomialEvalCosted_result costs 11 (by decide), plonkProofFromJointView,
    plonkPublicPolynomialsFromRows, pub, mask, materializePlonkMaskView]
  rfl

end Zcash.Snark.ZeroKnowledge
