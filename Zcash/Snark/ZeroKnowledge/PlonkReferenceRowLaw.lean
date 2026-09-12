import Zcash.Snark.ZeroKnowledge.PlonkProductChallenges
import Zcash.Snark.ZeroKnowledge.PlonkRowPrerequisites
import Zcash.Snark.ZeroKnowledge.PlonkFresh

/-!
# The concrete reference row experiment inside the joint simulation

The analysis retains the complete challenge record and selected private row tape.
These private tapes are not a disclosed verifier view. Their joint law realizes the
existing averaged invalid-row term exactly. Factoring the two product challenges
then applies the concrete denominator bound under that same full challenge law.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder URS)
open Zcash.Common
open CompPoly.CPolynomial
open scoped ENNReal

/-- Analysis state: the full public challenge tape and the selected private replacement-row tape. -/
abbrev PlonkReferenceRowTape (actions k : ℕ) := Challenges k Fp × (Fin (126 * actions) → Fp)

/-- The challenge law and independent uniform selected row tape used by the invalid-row term. -/
noncomputable def plonkReferenceRowTapeLaw {k : ℕ} (actions : ℕ) (law : PMF (Challenges k Fp)) :
    PMF (PlonkReferenceRowTape actions k) :=
  law.bind fun ch => (PMF.uniformOfFintype (Fin (126 * actions) → Fp)).map (Prod.mk ch)

/-- The full analysis law can draw its two product challenges after the other independent tapes. -/
theorem plonkReferenceRowTapeLaw_products (actions k : ℕ) :
    plonkReferenceRowTapeLaw actions (widePlonkChallenges k) =
      (plonkReferenceRowTapeLaw actions (widePlonkOtherChallenges k)).bind fun state =>
        wideProductChallenges.map fun coins => (withProductChallenges state.1 coins, state.2) := by
  simp only [plonkReferenceRowTapeLaw, widePlonkChallenges_products,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (fun next : Challenges k Fp → PMF (PlonkReferenceRowTape actions k) =>
    (widePlonkOtherChallenges k).bind next)
  funext ch
  exact PMF.bind_comm wideProductChallenges (PMF.uniformOfFintype (Fin (126 * actions) → Fp))
    (fun coins tape => PMF.pure (withProductChallenges ch coins, tape))

/-- The computed denominator bound holds under the same complete challenge law as the joint simulation. -/
theorem plonkReferenceRowTapeLaw_denominators_bad_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    (plonkReferenceRowTapeLaw actions (widePlonkChallenges k)).toOuterMeasure {state |
      ¬ plonkProductDenominatorsNonzero pub (plonkTotalColumnRows vk pub witness state.1 state.2)
        vk.permutationChunks state.1.beta state.1.gamma} ≤
      ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        2 * challenge255Bias := by
  rw [plonkReferenceRowTapeLaw_products, PMF.toOuterMeasure_bind_apply]
  have hpoint (state : PlonkReferenceRowTape actions k) :
      (wideProductChallenges.map fun coins => (withProductChallenges state.1 coins, state.2)).toOuterMeasure
        {entry | ¬ plonkProductDenominatorsNonzero pub
          (plonkTotalColumnRows vk pub witness entry.1 entry.2) vk.permutationChunks entry.1.beta entry.1.gamma} ≤
        ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias := by
    rw [PMF.toOuterMeasure_map_apply]
    exact widePlonkProductDenominators_bad_le vk pub witness state.1 state.2
  calc
    _ ≤ ∑' state, (plonkReferenceRowTapeLaw actions (widePlonkOtherChallenges k)) state *
        (((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias) :=
      ENNReal.tsum_le_tsum fun state => mul_le_mul_right (hpoint state) _
    _ = _ := by
      rw [ENNReal.tsum_mul_right, (plonkReferenceRowTapeLaw actions (widePlonkOtherChallenges k)).tsum_coe,
        _root_.one_mul]

/-- The existing average invalid-row term is exactly the concrete reference tape's failed-division event. -/
theorem freshPlonkInvalidRowMass_referenceRows {actions : ℕ} {G : Type*} [AddCommGroup G]
    (urs : URS G) (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    freshPlonkInvalidRowMass urs law (plonkTotalColumnConstructor vk pub witness) [] vk pub =
      (plonkReferenceRowTapeLaw actions law).toOuterMeasure {state |
        ¬ (X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub state.1
          (plonkTotalColumnRows vk pub witness state.1 state.2)} := by
  rw [freshPlonkInvalidRowMass, plonkReferenceRowTapeLaw, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro ch
  congr 1
  rw [plonkInvalidRowMass, ← uniformTapePlonkTotalColumnRows vk pub witness ch,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  rfl

/-- The remaining probability that sorting, gate preservation, or the packed copy identity fails. -/
noncomputable def plonkRowPrerequisiteFailureMass {actions k : ℕ} {G : Type*} [Zero G]
    (law : PMF (Challenges k Fp)) (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) : ℝ≥0∞ :=
  (plonkReferenceRowTapeLaw actions law).toOuterMeasure
    {state | ¬ PlonkRowPrerequisites vk pub witness state.1 state.2}

/-- The invalid-row mass is bounded by the explicit remaining prerequisites and computed denominators. -/
theorem freshPlonkInvalidRowMass_le_prerequisites {actions : ℕ} {G : Type*} [AddCommGroup G]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hchunks : vk.permutationChunks.length = 3) :
    freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub ≤
      plonkRowPrerequisiteFailureMass (widePlonkChallenges urs.k) vk pub witness +
        ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias := by
  rw [freshPlonkInvalidRowMass_referenceRows]
  let law := plonkReferenceRowTapeLaw actions (widePlonkChallenges urs.k)
  let unready : Set (PlonkReferenceRowTape actions urs.k) :=
    {state | ¬ PlonkRowPrerequisites vk pub witness state.1 state.2}
  let zeroDen : Set (PlonkReferenceRowTape actions urs.k) :=
    {state | ¬ plonkProductDenominatorsNonzero pub (plonkTotalColumnRows vk pub witness state.1 state.2)
      vk.permutationChunks state.1.beta state.1.gamma}
  have hcover : {state : PlonkReferenceRowTape actions urs.k |
      ¬ (X ^ 2048 - 1 : CPoly) ∣ plonkConstraintNumerator vk pub state.1
        (plonkTotalColumnRows vk pub witness state.1 state.2)} ⊆ unready ∪ zeroDen := by
    intro state hbad
    exact plonkTotalColumnRows_invalid_cover vk pub witness state.1 state.2 hchunks hbad
  calc
    _ ≤ law.toOuterMeasure (unready ∪ zeroDen) := MeasureTheory.measure_mono hcover
    _ ≤ law.toOuterMeasure unready + law.toOuterMeasure zeroDen := MeasureTheory.measure_union_le _ _
    _ ≤ law.toOuterMeasure unready +
        (((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias) :=
      add_le_add le_rfl (plonkReferenceRowTapeLaw_denominators_bad_le vk pub witness)
    _ = _ := (_root_.add_assoc _ _ _).symm

end Zcash.Snark.ZeroKnowledge
