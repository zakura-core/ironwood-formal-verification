import Zcash.Snark.ZeroKnowledge.SparseIpa
import Zcash.Snark.Soundness.Ipa.IpaSoundness
import Mathlib.Tactic.Module

/-!
# Honest IPA messages and the final verifier equation

This is the coefficient-vector algorithm in the pinned description: the witness folds by
`u⁻¹`, the public vectors by `u`, and each left/right message has its own additive blind.
Challenges are supplied as inputs. This models the algebra before encoding and terminal failures,
not the Fiat–Shamir challenge-generation procedure.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Fold a public generator or evaluation vector by the round challenges. -/
def publicFold : (k : ℕ) → (Fin k → F) → (Fin (2 ^ k) → G) → G
  | 0, _, values => values 0
  | k + 1, rounds, values =>
      publicFold k (fun j => rounds j.succ)
        (loHalf values + rounds 0 • hiHalf values)

/-- One pair of unblinded cross terms, including the evaluation-generator contribution. -/
def ipaCrossTerms {k : ℕ} (z : F) (U : G)
    (a b : Fin (2 ^ (k + 1)) → F) (g : Fin (2 ^ (k + 1)) → G) : G × G :=
  (commitGen (loHalf g) (hiHalf a) + (z * innerProduct (hiHalf a) (loHalf b)) • U,
    commitGen (hiHalf g) (loHalf a) + (z * innerProduct (loHalf a) (hiHalf b)) • U)

/-- All unblinded cross terms, computed from the successively folded vectors. -/
def ipaCoreMessages (z : F) (U : G) :
    (k : ℕ) → (Fin k → F) → (Fin (2 ^ k) → F) → (Fin (2 ^ k) → F) →
      (Fin (2 ^ k) → G) → (Fin k → G × G)
  | 0, _, _, _, _ => Fin.elim0
  | k + 1, rounds, a, b, g =>
      Fin.cons (ipaCrossTerms z U a b g)
        (ipaCoreMessages z U k (fun j => rounds j.succ)
          (foldVec (loHalf a) (hiHalf a) (rounds 0)⁻¹)
          (loHalf b + rounds 0 • hiHalf b)
          (loHalf g + rounds 0 • hiHalf g))

/-- The public linear combination of left/right messages in the verifier equation. -/
def ipaMessageSum {k : ℕ} (rounds : Fin k → F) (messages : Fin k → G × G) : G :=
  ∑ j, ((rounds j)⁻¹ • (messages j).1 + rounds j • (messages j).2)

/-- One actual prover fold preserves the combined commitment/evaluation equation. -/
theorem ipaCrossTerms_equation {k : ℕ} (z : F) (U : G)
    (a b : Fin (2 ^ (k + 1)) → F) (g : Fin (2 ^ (k + 1)) → G)
    (u : F) (hu : u ≠ 0) :
    commitGen g a + (z * innerProduct a b) • U +
        (u⁻¹ • (ipaCrossTerms z U a b g).1 + u • (ipaCrossTerms z U a b g).2) =
      commitGen (loHalf g + u • hiHalf g) (foldVec (loHalf a) (hiHalf a) u⁻¹) +
        (z * innerProduct (foldVec (loHalf a) (hiHalf a) u⁻¹)
          (loHalf b + u • hiHalf b)) • U := by
  have hgroup := commitGen_round (loHalf g) (hiHalf g) (loHalf a) (hiHalf a) hu
  rw [← commitGen_split] at hgroup
  have hfield := commitGen_round (loHalf b) (hiHalf b) (loHalf a) (hiHalf a) hu
  rw [← commitGen_split] at hfield
  change innerProduct (loHalf a + u⁻¹ • hiHalf a) (loHalf b + u • hiHalf b) =
    innerProduct a b + u * innerProduct (loHalf a) (hiHalf b) +
      u⁻¹ * innerProduct (hiHalf a) (loHalf b) at hfield
  rw [foldVec, hgroup, hfield]
  simp only [ipaCrossTerms]
  module

/-- Telescoping every actual prover fold yields the complete unblinded IPA equation. -/
theorem ipaCoreMessages_equation (z : F) (U : G) (k : ℕ) (rounds : Fin k → F)
    (a b : Fin (2 ^ k) → F) (g : Fin (2 ^ k) → G) (hu : ∀ j, rounds j ≠ 0) :
    commitGen g a + (z * innerProduct a b) • U +
        ipaMessageSum rounds (ipaCoreMessages z U k rounds a b g) =
      foldByRounds k rounds a • publicFold k rounds g +
        (z * foldByRounds k rounds a * publicFold k rounds b) • U := by
  induction k with
  | zero =>
    simp [ipaMessageSum, commitGen, innerProduct, foldByRounds, publicFold, mul_assoc]
  | succ k ih =>
    have htail : ∀ j : Fin k, rounds j.succ ≠ 0 := fun j => hu j.succ
    have hrest := ih (fun j => rounds j.succ)
      (foldVec (loHalf a) (hiHalf a) (rounds 0)⁻¹)
      (loHalf b + rounds 0 • hiHalf b) (loHalf g + rounds 0 • hiHalf g) htail
    rw [foldByRounds, publicFold, publicFold, ← hrest]
    simp only [ipaMessageSum, ipaCoreMessages, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [← add_assoc, ipaCrossTerms_equation z U a b g (rounds 0) (hu 0)]

/-- Private IPA coins: one mask-commitment blind and one left/right pair per round. -/
abbrev IpaBlinds (k : ℕ) (F : Type*) := F × (Fin k → F × F)

/-- Add the independent Pedersen blinds to every computed cross term. -/
def blindIpaMessages {k : ℕ} (W : G) (messages : Fin k → G × G)
    (blinds : Fin k → F × F) : Fin k → G × G := fun j =>
  ((messages j).1 + (blinds j).1 • W, (messages j).2 + (blinds j).2 • W)

/-- The actual accumulated blind, including the incoming polynomial's blind. -/
def ipaFinalBlind {k : ℕ} (rho xi : F) (rounds : Fin k → F) (blinds : IpaBlinds k F) : F :=
  rho + xi * blinds.1 +
    ∑ j, ((rounds j)⁻¹ * (blinds.2 j).1 + rounds j * (blinds.2 j).2)

/-- Blinding each message adds exactly the matching terms to the final aggregate blind. -/
theorem ipaMessageSum_blind {k : ℕ} (W : G) (rounds : Fin k → F)
    (messages : Fin k → G × G) (blinds : Fin k → F × F) :
    ipaMessageSum rounds (blindIpaMessages W messages blinds) =
      ipaMessageSum rounds messages +
        (∑ j, ((rounds j)⁻¹ * (blinds j).1 + rounds j * (blinds j).2)) • W := by
  simp only [ipaMessageSum, blindIpaMessages, smul_add, smul_smul, Finset.sum_smul,
    add_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  abel

end Zcash.Snark.ZeroKnowledge
