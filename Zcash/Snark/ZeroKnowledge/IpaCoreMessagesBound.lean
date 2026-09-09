import Zcash.Snark.ZeroKnowledge.IpaCoreMessagesCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Common next-vector access price, including inverse witness folding and public group folding. -/
def ipaNextVectorReadBudget (costs : FieldOperationCosts)
    (groupAdd groupScale k roundRead valueRead : ℕ) : ℕ :=
  2 * valueRead + roundRead + costs.inverse + costs.add + costs.multiply +
    groupAdd + groupScale + 2 * k + 8

/-- Explicit recursion for the complete real-message reader; all rounds are fixed at eleven for Action. -/
def ipaCoreMessagesCostBudget (costs : FieldOperationCosts)
    (groupAdd groupScale zRead uRead : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, roundRead, valueRead =>
    ipaCrossTermsCostBudget costs groupAdd groupScale k valueRead zRead uRead +
      ipaCoreMessagesCostBudget costs groupAdd groupScale zRead uRead k (roundRead + 1)
        (ipaNextVectorReadBudget costs groupAdd groupScale k roundRead valueRead) + 5

/-- Every original real-message reader invocation has the complete recursive budget. -/
theorem ipaCoreMessagesCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale : ℕ)
    (z : F × ℕ) (U : G × ℕ) (k : ℕ) (rounds : Fin k → F × ℕ)
    (a b : Fin (2 ^ k) → F × ℕ) (g : Fin (2 ^ k) → G × ℕ) (roundRead valueRead : ℕ)
    (hround : ∀ i, (rounds i).2 ≤ roundRead) (ha : ∀ i, (a i).2 ≤ valueRead)
    (hb : ∀ i, (b i).2 ≤ valueRead) (hg : ∀ i, (g i).2 ≤ valueRead) (index : Fin k) :
    (ipaCoreMessagesCosted costs groupAdd groupScale z U k rounds a b g index).2 ≤
      ipaCoreMessagesCostBudget costs groupAdd groupScale z.2 U.2 k roundRead valueRead := by
  induction k generalizing roundRead valueRead with
  | zero => exact Fin.elim0 index
  | succ k ih =>
    have hc := ipaCrossTermsCosted_cost_le costs groupAdd groupScale z U a b g valueRead ha hb hg
    have hnextA (i : Fin (2 ^ k)) :
        (ipaFoldReaderCosted costs.add costs.multiply (ipaInverseRoundCosted costs.inverse (rounds 0)) a i).2 ≤
          ipaNextVectorReadBudget costs groupAdd groupScale k roundRead valueRead := by
      have h := ipaFoldReaderCosted_cost_le costs.add costs.multiply
        (ipaInverseRoundCosted costs.inverse (rounds 0)) a valueRead ha i
      rewrite [ipaInverseRoundCosted_cost] at h
      have hr := hround 0
      unfold ipaNextVectorReadBudget
      omega
    have hnextB (i : Fin (2 ^ k)) :
        (ipaFoldReaderCosted costs.add costs.multiply (rounds 0) b i).2 ≤
          ipaNextVectorReadBudget costs groupAdd groupScale k roundRead valueRead := by
      have h := ipaFoldReaderCosted_cost_le costs.add costs.multiply (rounds 0) b valueRead hb i
      have hr := hround 0
      unfold ipaNextVectorReadBudget
      omega
    have hnextG (i : Fin (2 ^ k)) :
        (ipaFoldReaderCosted groupAdd groupScale (rounds 0) g i).2 ≤
          ipaNextVectorReadBudget costs groupAdd groupScale k roundRead valueRead := by
      have h := ipaFoldReaderCosted_cost_le groupAdd groupScale (rounds 0) g valueRead hg i
      have hr := hround 0
      unfold ipaNextVectorReadBudget
      omega
    have hrest (j : Fin k) := ih
      (fun i => ((rounds i.succ).1, (rounds i.succ).2 + 1))
      (ipaFoldReaderCosted costs.add costs.multiply (ipaInverseRoundCosted costs.inverse (rounds 0)) a)
      (ipaFoldReaderCosted costs.add costs.multiply (rounds 0) b)
      (ipaFoldReaderCosted groupAdd groupScale (rounds 0) g)
      (roundRead + 1) (ipaNextVectorReadBudget costs groupAdd groupScale k roundRead valueRead)
      (fun i => Nat.add_le_add_right (hround i.succ) 1) hnextA hnextB hnextG j
    refine Fin.cases ?_ (fun j => ?_) index
    · change (ipaCrossTermsCosted costs groupAdd groupScale z U a b g).2 + 5 ≤ _
      simp only [ipaCoreMessagesCostBudget]
      omega
    · change (ipaCrossTermsCosted costs groupAdd groupScale z U a b g).2 +
        (ipaCoreMessagesCosted costs groupAdd groupScale z U k _ _ _ _ j).2 + 5 ≤ _
      have hr := hrest j
      simp only [ipaCoreMessagesCostBudget]
      omega

/-- Increasing explicit access prices preserves the complete recursive budget. -/
theorem ipaCoreMessagesCostBudget_mono (costs : FieldOperationCosts) (groupAdd groupScale k : ℕ)
    {zRead uRead roundRead valueRead zRead' uRead' roundRead' valueRead' : ℕ}
    (hz : zRead ≤ zRead') (hu : uRead ≤ uRead') (hr : roundRead ≤ roundRead') (hv : valueRead ≤ valueRead') :
    ipaCoreMessagesCostBudget costs groupAdd groupScale zRead uRead k roundRead valueRead ≤
      ipaCoreMessagesCostBudget costs groupAdd groupScale zRead' uRead' k roundRead' valueRead' := by
  induction k generalizing roundRead valueRead roundRead' valueRead' with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [ipaCoreMessagesCostBudget]
    apply Nat.add_le_add_right
    apply Nat.add_le_add
    · unfold ipaCrossTermsCostBudget ipaCrossTermCostBudget
      gcongr
    · apply ih (Nat.add_le_add_right hr 1)
      unfold ipaNextVectorReadBudget
      gcongr

end Zcash.Snark.ZeroKnowledge
