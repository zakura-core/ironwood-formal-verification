import Zcash.Snark.ZeroKnowledge.PlonkComposition
import Zcash.Snark.ZeroKnowledge.IpaSimulator

/-!
# Executing the joint simulator from field coins

The simulator samples commitment points as multiples of `W`, samples column observation
vectors directly, reconstructs the public IPA opening, and runs the existing field-coin
IPA simulator. Its executable function has no witness, private row constructor, quotient
piece constructor, or discrete-log inverse argument.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- Uniform finite vectors give exactly the sequential column-view law. -/
theorem uniformColumnViews_ofFn (d count : ℕ) :
    (PMF.uniformOfFintype (Fin count → Fin d → Fp)).map List.ofFn = uniformColumnViews d count := by
  induction count with
  | zero =>
    have h : (List.ofFn : (Fin 0 → Fin d → Fp) → List (Fin d → Fp)) = fun _ => [] := by
      funext f
      simp
    rw [h]
    exact PMF.map_const _ _
  | succ count ih =>
    let e := (Fin.consEquiv (fun _ : Fin (count + 1) => Fin d → Fp)).symm
    have hfactor : (List.ofFn : (Fin (count + 1) → Fin d → Fp) → List (Fin d → Fp)) =
        (fun pair : (Fin d → Fp) × (Fin count → Fin d → Fp) => pair.1 :: List.ofFn pair.2) ∘ e := by
      funext f
      change List.ofFn f = f 0 :: List.ofFn (fun i => f i.succ)
      exact List.ofFn_succ
    rw [hfactor, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
      ← Zcash.independentProductPMF_uniform, Zcash.independentProductPMF, PMF.map_bind]
    unfold uniformColumnViews
    congr 1
    funext first
    simp only [PMF.map_comp, Function.comp_def]
    rw [← ih, PMF.map_comp]
    rfl

/-- Field coins for the jointly uniform point family, column observations, and two masked values. -/
abbrev PlonkMaskSimulatorCoins (actions : ℕ) :=
  (Fin (22 * actions + 10) → Fp) × ((Fin (22 * actions) → Fin 5 → Fp) × (Fp × Fp))

section Algorithms

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Execute the public pre-IPA simulator without enumerating group elements. -/
def plonkMaskSimulatorFromCoins {actions : ℕ} (W : G) (coins : PlonkMaskSimulatorCoins actions) :
    PreIpaMaskView 5 (22 * actions + 10) G :=
  (fun i => coins.1 i • W, List.ofFn coins.2.1, coins.2.2)

/-- Execute the entire joint simulator from public parameters and field coins. -/
def plonkJointSimulatorFromCoins {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (maskCoins : PlonkMaskSimulatorCoins actions) (roundCoins : Fin urs.k → Fp × Fp)
    (scalarCoin finalBlind : Fp) :
    PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G :=
  let view := plonkMaskSimulatorFromCoins urs.w maskCoins
  let input := plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view
  (view, ipaSimulatorFromCoins input roundCoins scalarCoin finalBlind)

end Algorithms

section Distributions

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Run the pre-IPA simulator using only independent uniform field coins. -/
noncomputable def idealPlonkMaskSimulatorFromFieldCoins {actions : ℕ} (W : G) :
    PMF (PreIpaMaskView 5 (22 * actions + 10) G) :=
  (PMF.uniformOfFintype (PlonkMaskSimulatorCoins actions)).map (plonkMaskSimulatorFromCoins W)

/-- Scalar-multiple point sampling and direct observation sampling implement the ideal public view. -/
theorem idealPlonkMaskSimulatorFromFieldCoins_eq [Fintype G] {actions : ℕ} (W : G)
    (hW : Function.Bijective (fun r : Fp => r • W)) :
    idealPlonkMaskSimulatorFromFieldCoins (actions := actions) W =
      preIpaMaskSimulator (G := G) 5 (22 * actions) (22 * actions + 10) := by
  have hpoints : (PMF.uniformOfFintype (Fin (22 * actions + 10) → Fp)).map
      (fun coins => fun i => coins i • W) = PMF.uniformOfFintype (Fin (22 * actions + 10) → G) := by
    have hfun : (fun coins : Fin (22 * actions + 10) → Fp => fun i => coins i • W) =
        blindedCommitments W (fun _ : Fin (22 * actions + 10) => (0 : G)) := by
      funext coins i
      exact (zero_add _).symm
    rw [hfun]
    exact blindedCommitments_uniform (F := Fp) W (fun _ => 0) hW
  rw [idealPlonkMaskSimulatorFromFieldCoins,
    ← Zcash.independentProductPMF_uniform (A := Fin (22 * actions + 10) → Fp)
      (B := (Fin (22 * actions) → Fin 5 → Fp) × (Fp × Fp)),
    ← Zcash.independentProductPMF_uniform (A := Fin (22 * actions) → Fin 5 → Fp) (B := Fp × Fp),
    preIpaMaskSimulator, ← hpoints, ← uniformColumnViews_ofFn]
  simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, plonkMaskSimulatorFromCoins]

/-- Run both stages of the joint simulator using their field-coin implementations. -/
noncomputable def idealPlonkJointSimulatorFromFieldCoins {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp) :
    PMF (PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G) :=
  (idealPlonkMaskSimulatorFromFieldCoins urs.w).bind fun view =>
    (idealIpaSimulatorFromFieldCoins
      (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view)).map (Prod.mk view)

/-- Expanding those field draws runs exactly the computable joint simulator above. -/
theorem idealPlonkJointSimulatorFromFieldCoins_program {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp) :
    idealPlonkJointSimulatorFromFieldCoins urs pub x x1 x2 x4 q xi z rounds expectedHx =
      (PMF.uniformOfFintype (PlonkMaskSimulatorCoins actions)).bind fun maskCoins =>
        (PMF.uniformOfFintype ((Fin urs.k → Fp × Fp) × Fp)).bind fun free =>
          (PMF.uniformOfFintype Fp).map fun scalarCoin =>
            plonkJointSimulatorFromCoins urs pub x x1 x2 x4 q xi z rounds expectedHx
              maskCoins free.1 scalarCoin free.2 := by
  simp only [idealPlonkJointSimulatorFromFieldCoins, idealPlonkMaskSimulatorFromFieldCoins,
    PMF.bind_map, idealIpaSimulatorFromFieldCoins, PMF.map_bind, PMF.map_comp,
    Function.comp_def, plonkJointSimulatorFromCoins]

/-- The executable field-coin simulator has exactly the joint law used in the simulation theorem. -/
theorem idealPlonkJointSimulatorFromFieldCoins_eq [Fintype G] {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    idealPlonkJointSimulatorFromFieldCoins urs pub x x1 x2 x4 q xi z rounds expectedHx =
      idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx := by
  unfold idealPlonkJointSimulatorFromFieldCoins
  have htail (view : PreIpaMaskView 5 (22 * actions + 10) G) :
      idealIpaSimulatorFromFieldCoins (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view) =
        idealIpaSimulator (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view) := by
    apply idealIpaSimulatorFromFieldCoins_eq
    exact hW
  simp_rw [htail]
  rw [idealPlonkMaskSimulatorFromFieldCoins_eq urs.w hW]
  rfl

end Distributions

end Zcash.Snark.ZeroKnowledge
