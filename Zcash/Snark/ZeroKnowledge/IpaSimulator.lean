import Zcash.Snark.ZeroKnowledge.IpaSimulation

/-!
# Executing the IPA simulator from field coins

The distribution proof uses uniform group points. This file implements those draws as
scalar multiples of `W` and implements the public-zero test with decidable field equality.
The resulting algorithm takes only public data and field coins; no inverse of the
discrete-log bijection appears in its computational content.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Nonzero `W` generates the group when its cardinality equals that of the scalar field. -/
theorem blinding_bijective_of_card_eq [Fintype F] [Fintype G] (W : G) (hW : W ≠ 0)
    (hcard : Fintype.card G = Fintype.card F) :
    Function.Bijective (fun r : F => r • W) := by
  have hinj : Function.Injective (fun r : F => r • W) := smul_left_injective F hW
  refine ⟨hinj, ?_⟩
  by_contra hsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective _ hinj hsurj
  rw [hcard] at hlt
  exact (lt_irrefl _ hlt)

/-- The scalar simulator's executable public case distinction. -/
def chooseIpaScalar [DecidableEq F] {k : ℕ} (q : F) (rounds : Fin k → F) (coin : F) : F :=
  if ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val) then 0 else coin

/-- One uniform field coin implements the scalar law used by the simulation theorem. -/
theorem chooseIpaScalar_uniform [DecidableEq F] [Fintype F] {k : ℕ}
    (q : F) (rounds : Fin k → F) :
    (PMF.uniformOfFintype F).map (chooseIpaScalar q rounds) =
      idealSparseIpaScalar q rounds := by
  classical
  by_cases h : ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val)
  · have hf : chooseIpaScalar q rounds = fun _ => 0 := by
      funext coin
      simp [chooseIpaScalar, h]
    rw [hf, idealSparseIpaScalar, if_pos h]
    exact PMF.map_const _ _
  · have hf : chooseIpaScalar q rounds = id := by
      funext coin
      simp [chooseIpaScalar, h]
    rw [hf, PMF.map_id, idealSparseIpaScalar, if_neg h]

/-- The joint simulator as a computable function of public inputs and field coins. -/
def ipaSimulatorFromCoins [DecidableEq F] {k : ℕ} (pub : IpaPublic k F G)
    (roundCoins : Fin k → F × F) (scalarCoin finalBlind : F) : IpaTranscript k F G :=
  completeIpaTranscript pub
    (blindIpaMessages pub.W (fun _ => (0, 0)) roundCoins)
    (chooseIpaScalar pub.point pub.rounds scalarCoin) finalBlind

/-- Run the executable simulator with independent uniform field coins. -/
noncomputable def idealIpaSimulatorFromFieldCoins [DecidableEq F] [Fintype F] {k : ℕ}
    (pub : IpaPublic k F G) : PMF (IpaTranscript k F G) :=
  (PMF.uniformOfFintype ((Fin k → F × F) × F)).bind fun free =>
    (PMF.uniformOfFintype F).map fun scalarCoin =>
      ipaSimulatorFromCoins pub free.1 scalarCoin free.2

/-- Field-coin simulation has exactly the public simulator's law. -/
theorem idealIpaSimulatorFromFieldCoins_eq [DecidableEq F] [Fintype F] [Fintype G] {k : ℕ}
    (pub : IpaPublic k F G) (hW : Function.Bijective (fun r : F => r • pub.W)) :
    idealIpaSimulatorFromFieldCoins pub = idealIpaSimulator pub := by
  let e : ((Fin k → F × F) × F) ≃ ((Fin k → G × G) × F) :=
    Equiv.prodCongr (ipaMessageBlindsEquiv pub.W (fun _ => (0, 0)) hW) (Equiv.refl F)
  unfold idealIpaSimulatorFromFieldCoins
  calc
    _ = (PMF.uniformOfFintype ((Fin k → F × F) × F)).bind fun free =>
        (idealSparseIpaScalar pub.point pub.rounds).map fun c =>
          completeIpaTranscript pub (e free).1 c (e free).2 := by
      congr 1
      funext free
      change (PMF.uniformOfFintype F).map
        ((fun c => completeIpaTranscript pub (e free).1 c (e free).2) ∘
          chooseIpaScalar pub.point pub.rounds) = _
      rw [← PMF.map_comp, chooseIpaScalar_uniform]
    _ = ((PMF.uniformOfFintype ((Fin k → F × F) × F)).map e).bind fun free =>
        (idealSparseIpaScalar pub.point pub.rounds).map fun c =>
          completeIpaTranscript pub free.1 c free.2 := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by rw [Zcash.map_uniformOfFintype_equiv]; rfl

end Zcash.Snark.ZeroKnowledge
