import Zcash.Snark.ZeroKnowledge.RoutedProofCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimInputBounds

/-! # A complete envelope for all routed proof-field producers -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A common polynomial price for every actual route and complete input producer. -/
def routedProofReadBudget (actions columns equal read access : ℕ) : ℕ :=
  5 * (4 * actions * actions + 260 * actions + 22 * actions * (equal + 2) +
    2 * columns + read + access + 15) + access + 200

/-- Every field of the routed proof satisfies the stated complete producer envelope. -/
theorem plonkRoutedProofCosts_readBound (equal read : ℕ) {actions k : ℕ} {G : Type*}
    (instances : Fin actions → Fp × ℕ) (fixed : Fin 29 → Fp × ℕ) (sigma : Fin 15 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (points : Fin (22 * actions + 10) → G × ℕ)
    (rEval : Fp × ℕ) (groupValues : Fin 5 → Fp × ℕ)
    (tail : IpaTranscript k (Fp × ℕ) (G × ℕ)) (access : ℕ)
    (hinstances : ∀ action, (instances action).2 ≤ access)
    (hfixed : ∀ column, (fixed column).2 ≤ access)
    (hsigma : ∀ column, (sigma column).2 ≤ access)
    (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ access)
    (hpoints : ∀ index, (points index).2 ≤ access)
    (hrEval : rEval.2 ≤ access)
    (hgroups : ∀ group, (groupValues group).2 ≤ access)
    (hmask : tail.maskCommitment.2 ≤ access)
    (hrounds : ∀ round, (tail.messages round).1.2 ≤ access ∧ (tail.messages round).2.2 ≤ access)
    (hscalar : tail.scalar.2 ≤ access) (hblind : tail.blind.2 ≤ access) :
    ProofFieldReadBound
      (plonkRoutedProofCosts equal read instances fixed sigma views points rEval groupValues tail)
      (routedProofReadBudget actions views.length equal read access) := by
  have hcommon : access ≤ routedProofReadBudget actions views.length equal read access := by
    unfold routedProofReadBudget
    omega
  have hcolumn (id : PrivateColumnId actions) :
      (plonkColumnEntryCosted equal points id).2 ≤
        routedProofReadBudget actions views.length equal read access := by
    have h := plonkColumnEntryCosted_cost_le equal points id access hpoints
    unfold routedProofReadBudget
    omega
  constructor
  · intro action column
    exact hcolumn (.advice action column)
  · intro action lookup
    exact hcolumn (.lookupInput action lookup)
  · intro action lookup
    exact hcolumn (.lookupTable action lookup)
  · intro action set
    exact hcolumn (.permutationProduct action set)
  · intro action lookup
    exact hcolumn (.lookupProduct action lookup)
  · exact (plonkLinearEntryCosted_cost_le points access hpoints).trans (by
      unfold routedProofReadBudget
      omega)
  · intro piece
    exact (plonkPieceEntryCosted_cost_le points piece access hpoints).trans (by
      unfold routedProofReadBudget
      omega)
  · intro action query
    exact (hinstances action).trans hcommon
  · intro action query
    exact (plonkAdviceClaimCosted_cost_le (actions := actions) equal read views action query access hviews).trans (by
      unfold routedProofReadBudget
      omega)
  · intro query
    exact (fixedClaimReaderCosted_cost_le fixed query access hfixed).trans (by
      unfold routedProofReadBudget
      omega)
  · exact hrEval.trans hcommon
  · intro column
    exact (hsigma column).trans hcommon
  · intro action set
    have h := payPermSetProducer_readBound (plonkPermutationSetCosted (actions := actions) equal read views action set) _ 1
      (plonkPermutationSetCosted_cost_le (actions := actions) equal read views action set access hviews)
      (plonkPermutationSetCosted_readBound (actions := actions) equal read views action set)
    exact permSetReadBound_mono h (by
      dsimp only [routedProofReadBudget]
      omega)
  · intro action lookup
    have h := payLookupProducer_readBound (plonkLookupEvalCosted (actions := actions) equal read views action lookup) _ 1
      (plonkLookupEvalCosted_cost_le (actions := actions) equal read views action lookup access hviews)
      (plonkLookupEvalCosted_readBound (actions := actions) equal read views action lookup)
    exact lookupEvalReadBound_mono h (by
      dsimp only [routedProofReadBudget]
      omega)
  · exact (plonkQuotientPrimeEntryCosted_cost_le points access hpoints).trans (by
      unfold routedProofReadBudget
      omega)
  · intro group
    exact (hgroups group).trans hcommon
  · exact hmask.trans hcommon
  · intro round
    exact ⟨((hrounds round).1).trans hcommon, ((hrounds round).2).trans hcommon⟩
  · exact hscalar.trans hcommon
  · exact hblind.trans hcommon

end Zcash.Snark.ZeroKnowledge
