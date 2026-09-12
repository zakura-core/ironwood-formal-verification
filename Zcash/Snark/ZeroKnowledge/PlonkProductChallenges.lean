import Zcash.Snark.ZeroKnowledge.PlonkChallenges
import Zcash.Snark.ZeroKnowledge.PlonkProductBounds

/-!
# Separate the product coins from the complete independent challenge tape

The full challenge law already samples every coordinate independently. Reordering
those draws separates beta and gamma without replacing the other coordinates by
uniform field elements or paying their sampling biases again. This is an exact law
identity for the offline tape experiment, not a Fiat-Shamir independence assertion.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- The first explicit index reads the head of a challenge tape, exposing the product-challenge
prefix. -/
private theorem cons_mk_zero {n : ℕ} {F : Type*} (first : F) (rest : Fin n → F) (h : 0 < n + 1) :
    Fin.cons (α := fun _ : Fin (n + 1) => F) first rest ⟨0, h⟩ = first := rfl

/-- A successor index reads the remaining challenge tape, exposing the tail after product-challenge
insertion. -/
private theorem cons_mk_succ {n : ℕ} {F : Type*} (first : F) (rest : Fin n → F)
    (i : ℕ) (h : i + 1 < n + 1) :
    Fin.cons (α := fun _ : Fin (n + 1) => F) first rest ⟨i + 1, h⟩ = rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

/-- Decode all non-product coins, placing zeros in the two slots to be sampled separately. -/
def plonkOtherChallengesFromTape {k : ℕ} (theta : Fp) (rest : Fin (k + 8) → Fp) : Challenges k Fp :=
  plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons 0 (Fin.cons 0 rest)))

/-- Inserting the product coins recovers the original challenge decoder exactly. -/
theorem plonkOtherChallengesFromTape_products {k : ℕ} (theta beta gamma : Fp)
    (rest : Fin (k + 8) → Fp) :
    withProductChallenges (plonkOtherChallengesFromTape theta rest) (Fin.cons beta (Fin.cons gamma Fin.elim0)) =
      plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons beta (Fin.cons gamma rest))) := by
  simp only [withProductChallenges, plonkOtherChallengesFromTape, plonkChallengesFromTape,
    Fin.cons_zero, Fin.cons_one, cons_mk_zero, cons_mk_succ, Challenges.mk.injEq, true_and]
  funext j
  have hindex : (⟨11 + j.val, by omega⟩ : Fin (k + 11)) =
      (⟨8 + j.val, by omega⟩ : Fin (k + 8)).succ.succ.succ := by
    apply Fin.ext
    change 11 + j.val = 8 + j.val + 1 + 1 + 1
    omega
  rw [hindex]
  simp only [Fin.cons_succ]

/-- The independent wide-reduced theta and later challenge coins, with beta and gamma reserved. -/
noncomputable def widePlonkOtherChallenges (k : ℕ) : PMF (Challenges k Fp) :=
  fieldSample.bind fun theta =>
    (sampleFieldsWith (k + 8) (plonkOtherChallengesFromTape theta)).runFreshPMF fieldSample

/-- Sampling splits into three independent leading fields and the remaining tape, isolating theta,
beta, and gamma for the product bound. -/
private theorem sampleFieldsWith_run_three {A : Type*} (count : ℕ)
    (finish : (Fin (count + 3) → Fp) → A) (law : PMF Fp) :
    (sampleFieldsWith (count + 3) finish).runFreshPMF law =
      law.bind fun first => law.bind fun second => law.bind fun third =>
        (sampleFieldsWith count (fun rest => finish (Fin.cons first (Fin.cons second (Fin.cons third rest))))).runFreshPMF law := rfl

/-- A two-field sampler is exactly two independent draws, identifying the joint product-challenge
law. -/
private theorem sampleFieldsWith_run_two {A : Type*} (finish : (Fin 2 → Fp) → A) (law : PMF Fp) :
    (sampleFieldsWith 2 finish).runFreshPMF law =
      law.bind fun first => law.bind fun second => PMF.pure (finish (Fin.cons first (Fin.cons second Fin.elim0))) := rfl

/-- The full wide-reduced verifier tape separates exactly into the other coins and two fresh product coins. -/
theorem widePlonkChallenges_products (k : ℕ) :
    widePlonkChallenges k =
      (widePlonkOtherChallenges k).bind fun ch => wideProductChallenges.map (withProductChallenges ch) := by
  let tailLaw := (sampleFieldsWith (k + 8) id).runFreshPMF fieldSample
  have htail (theta beta gamma : Fp) :
      (sampleFieldsWith (k + 8) (fun rest =>
        plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons beta (Fin.cons gamma rest))))).runFreshPMF fieldSample =
      tailLaw.map (fun rest => plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons beta (Fin.cons gamma rest)))) :=
    sampleFieldsWith_map (k + 8) id
      (fun rest => plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons beta (Fin.cons gamma rest)))) fieldSample
  have hother (theta : Fp) :
      (sampleFieldsWith (k + 8) (plonkOtherChallengesFromTape theta)).runFreshPMF fieldSample =
        tailLaw.map (plonkOtherChallengesFromTape theta) :=
    sampleFieldsWith_map (k + 8) id (plonkOtherChallengesFromTape theta) fieldSample
  rw [widePlonkChallenges, sampleFieldsWith_run_three (k + 8)]
  simp_rw [htail]
  simp only [widePlonkOtherChallenges, hother, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (fun next : Fp → PMF (Challenges k Fp) => fieldSample.bind next)
  funext theta
  have hproduct (rest : Fin (k + 8) → Fp) :
      wideProductChallenges.map (withProductChallenges (plonkOtherChallengesFromTape theta rest)) =
        fieldSample.bind fun beta => fieldSample.bind fun gamma =>
          PMF.pure (plonkChallengesFromTape (k := k) (Fin.cons theta (Fin.cons beta (Fin.cons gamma rest)))) := by
    rw [wideProductChallenges, sampleFieldsWith_run_two]
    simp only [PMF.map_bind, PMF.pure_map, id_eq, plonkOtherChallengesFromTape_products]
  simp_rw [hproduct]
  simp only [PMF.map, Function.comp_def]
  conv_lhs =>
    arg 2
    ext beta
    rw [PMF.bind_comm fieldSample tailLaw]
  rw [PMF.bind_comm fieldSample tailLaw]

end Zcash.Snark.ZeroKnowledge
