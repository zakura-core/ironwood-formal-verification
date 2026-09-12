import Zcash.Common.RelationProbabilityCoins

/-!
# Joint hiding of independently blinded commitments

An independently uniform scalar blind makes a commitment uniform even when its unblinded
point depends on other private coins. Applying the change of variables to a whole family
proves independence from any separately disclosed function of those coins.

All challenges are supplied inputs here. This result does not justify conditioning a
Fiat–Shamir execution on challenges computed from these commitments.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A blinded point is a bijective reparameterization of its scalar blind. -/
noncomputable def blindPointEquiv (W offset : G)
    (hW : Function.Bijective (fun r : F => r • W)) : F ≃ G where
  toFun := fun r => offset + r • W
  invFun := fun point => (Equiv.ofBijective (fun r : F => r • W) hW).symm (point - offset)
  left_inv := by
    intro r
    change (Equiv.ofBijective (fun r : F => r • W) hW).symm ((offset + r • W) - offset) = r
    rw [add_sub_cancel_left]
    exact (Equiv.ofBijective (fun r : F => r • W) hW).symm_apply_apply r
  right_inv := by
    intro point
    change offset + (Equiv.ofBijective (fun r : F => r • W) hW)
      ((Equiv.ofBijective (fun r : F => r • W) hW).symm (point - offset)) = point
    rw [Equiv.apply_symm_apply]
    abel

/-- Independently blind each point in an indexed commitment family. -/
def blindedCommitments {I : Type*} (W : G) (cores : I → G) (blinds : I → F) : I → G :=
  fun i => cores i + blinds i • W

/-- The simultaneous change of variables from scalar blinds to blinded points. -/
noncomputable def commitmentBlindsEquiv {I : Type*} (W : G) (cores : I → G)
    (hW : Function.Bijective (fun r : F => r • W)) : (I → F) ≃ (I → G) :=
  Equiv.piCongrRight fun i => blindPointEquiv W (cores i) hW

/-- Uniform independent blinds hide the entire indexed family jointly. -/
theorem blindedCommitments_uniform {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype F] [Fintype G]
    (W : G) (cores : I → G) (hW : Function.Bijective (fun r : F => r • W)) :
    (PMF.uniformOfFintype (I → F)).map (blindedCommitments W cores) =
      PMF.uniformOfFintype (I → G) :=
  Zcash.map_uniformOfFintype_equiv (commitmentBlindsEquiv W cores hW)

/-- Retain both the blinded commitments and a disclosed function of the other private coins. -/
noncomputable def commitmentView {I A V : Type*} [Fintype I] [DecidableEq I] [Fintype F]
    (W : G) (cores : A → I → G) (disclose : A → V) (coins : PMF A) :
    PMF ((I → G) × V) :=
  coins.bind fun a =>
    (PMF.uniformOfFintype (I → F)).map fun blinds =>
      (blindedCommitments W (cores a) blinds, disclose a)

/-- The jointly blinded points are independent of the separately disclosed view.

The unblinded points may depend arbitrarily on the private coins and on a fixed witness.
No independence assumption between those points and the disclosure is needed. The scalar
blinds themselves must be independent of those coins. -/
theorem commitmentView_eq {I A V : Type*} [Fintype I] [DecidableEq I]
    [Fintype F] [Fintype G]
    (W : G) (cores : A → I → G) (disclose : A → V) (coins : PMF A)
    (hW : Function.Bijective (fun r : F => r • W)) :
    commitmentView (F := F) W cores disclose coins =
      Zcash.independentProductPMF (PMF.uniformOfFintype (I → G)) (coins.map disclose) := by
  have hfixed (a : A) :
      (PMF.uniformOfFintype (I → F)).map (fun blinds =>
          (blindedCommitments W (cores a) blinds, disclose a)) =
        (PMF.uniformOfFintype (I → G)).map (fun points => (points, disclose a)) := by
    change (PMF.uniformOfFintype (I → F)).map
        ((fun points => (points, disclose a)) ∘ blindedCommitments W (cores a)) = _
    rw [← PMF.map_comp, blindedCommitments_uniform W (cores a) hW]
  unfold commitmentView Zcash.independentProductPMF
  simp_rw [hfixed]
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm]

end Zcash.Snark.ZeroKnowledge
