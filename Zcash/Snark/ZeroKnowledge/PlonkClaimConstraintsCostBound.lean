import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCost
import Zcash.Snark.ZeroKnowledge.PlonkPreparedConstraintBudget

/-!
# Full cost of the original claim constraint computation

The complete bound derives preparation costs, stored-field access bounds, and
constraint-list sizes from their actual constructors. Its remaining reader
premises price public rows, disclosed observations, and supplied key trees;
challenge accesses are bounded explicitly as well.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Complete polynomial budget, including all input preparation and the ordered output list. -/
def plonkClaimConstraintsCostBudget (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    (actions viewCount access xAccess : ℕ) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (stride : ℕ) : ℕ :=
  let columnBudget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
    2 * viewCount + read + access + 15
  let queryAccess := publicRowEvaluationCostBudget costs access omegaAccess xAccess +
    columnBudget + access + 277
  let setBudget := 3 * (3 * columnBudget + 9) + 10
  let lookupBudget := 3 * (5 * columnBudget + access + access + 15) + 10
  let preparation := 2 * setBudget + layout.2 +
    3 * ((layout.1.map List.length).sum * (2 * queryAccess + 5) + 6) + 3 + lookupBudget
  let budget := plonkPreparedConstraintCostBudget costs node queryAccess gates.1 layout.1 inputs tables stride
  gates.2 + (actions * (preparation + budget + (gates.1.length + 23) + 3) + actions * actions + 1) + 1

/-- The actual query providers and argument constructors discharge the entire collection budget. -/
theorem plonkClaimConstraintsCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (beta gamma x delta theta : Fp × ℕ) (stride : ℕ) (l0 lLast lBlind : Fp × ℕ)
    (access : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ access)
    (hfixed : ∀ column row, (fixed column row).2 ≤ access)
    (hsigma : ∀ column row, (sigma column row).2 ≤ access)
    (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access)
    (hinputs : ∀ index, (inputs index).2 ≤ access) (htables : ∀ index, (tables index).2 ≤ access)
    (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access) (hx : x.2 ≤ access)
    (hdelta : delta.2 ≤ access) (htheta : theta.2 ≤ access)
    (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (plonkClaimConstraintsCosted costs node equal read omegaAccess instances fixed sigma views
      gates layout inputs tables beta gamma x delta theta stride l0 lLast lBlind).2 ≤
      plonkClaimConstraintsCostBudget costs node equal read omegaAccess actions views.length access x.2
        gates layout inputs tables stride := by
  let columnBudget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
    2 * views.length + read + access + 15
  let queryAccess := publicRowEvaluationCostBudget costs access omegaAccess x.2 +
    columnBudget + access + 277
  let setBudget := 3 * (3 * columnBudget + 9) + 10
  let lookupBudget := 3 * (5 * columnBudget + access + access + 15) + 10
  let preparation := 2 * setBudget + layout.2 +
    3 * ((layout.1.map List.length).sum * (2 * queryAccess + 5) + 6) + 3 + lookupBudget
  let budget := plonkPreparedConstraintCostBudget costs node queryAccess gates.1 layout.1 inputs tables stride
  let fixedQueries := plonkFixedQueryCosted costs omegaAccess fixed x
  let adviceQueries := plonkAdviceQueryCosted (actions := actions) equal read views
  let instanceQueries := fun action =>
    publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) x
  let sigmaQueries := publicRowQueryCosted costs omegaAccess sigma x
  let sets := plonkPermutationSetsCosted (actions := actions) equal read views
  let chunks := fun action => permutationQueryChunksCosted (instanceQueries action)
    (adviceQueries action) fixedQueries sigmaQueries (sets action) layout
  let lookups := fun action : Fin actions => plonkLookupInputsCosted equal read views action inputs tables
  have hunit : 1 ≤ queryAccess := by dsimp only [queryAccess]; omega
  have haccess : access ≤ queryAccess := by dsimp only [queryAccess]; omega
  have hf : ∀ index, (fixedQueries index).2 ≤ queryAccess := by
    intro index
    have h := plonkFixedQueryCosted_cost_le costs omegaAccess fixed x index access hfixed
    change (fixedQueries index).2 ≤ _ at h
    dsimp only [queryAccess]
    omega
  have ha : ∀ action index, (adviceQueries action index).2 ≤ queryAccess := by
    intro action index
    have h := plonkAdviceQueryCosted_cost_le equal read views action index access hviews
    change (adviceQueries action index).2 ≤ _ at h
    dsimp only [queryAccess, columnBudget]
    omega
  have hi : ∀ action index, (instanceQueries action index).2 ≤ queryAccess := by
    intro action index
    have h := publicRowQueryCosted_cost_le costs omegaAccess (fun _ : Fin 1 => instances action)
      x index access (fun _ => hinstances action)
    change (instanceQueries action index).2 ≤ _ at h
    dsimp only [queryAccess]
    omega
  have hs : ∀ index, (sigmaQueries index).2 ≤ queryAccess := by
    intro index
    have h := publicRowQueryCosted_cost_le costs omegaAccess sigma x index access hsigma
    change (sigmaQueries index).2 ≤ _ at h
    dsimp only [queryAccess]
    omega
  have hsets : ∀ action set, set ∈ (sets action).1 → permSetReadBound set queryAccess := by
    intro action set hmem
    exact permSetReadBound_mono (plonkPermutationSetsCosted_readBound equal read views action set hmem) hunit
  have hchunks : ∀ action chunk, chunk ∈ (chunks action).1 →
      permSetReadBound chunk.1 queryAccess ∧ ∀ pair ∈ chunk.2, pair.2 ≤ queryAccess := by
    intro action chunk hmem
    have h := permutationQueryChunksCosted_readBound (instanceQueries action) (adviceQueries action)
      fixedQueries sigmaQueries (sets action) layout
      (plonkPermutationSetsCosted_readBound equal read views action) chunk hmem
    exact ⟨permSetReadBound_mono h.1 hunit, fun pair hp => (h.2 pair hp).trans hunit⟩
  have hlookups : ∀ action lookup, lookup ∈ (lookups action).1 → lookupEvalReadBound lookup.1 queryAccess := by
    intro action lookup hmem
    exact lookupEvalReadBound_mono
      (plonkLookupInputsCosted_readBound equal read views action inputs tables lookup hmem) hunit
  have hprepare : ∀ action, (sets action).2 + (chunks action).2 + (lookups action).2 ≤ preparation := by
    intro action
    have hset := plonkPermutationSetsCosted_cost_le equal read views action access hviews
    have hlookup := plonkLookupInputsCosted_cost_le equal read views action inputs tables access access access
      hviews hinputs htables
    have hchunk := permutationQueryChunksCosted_cost_le (instanceQueries action) (adviceQueries action)
      fixedQueries sigmaQueries (sets action) layout queryAccess (hi action) (ha action) hf hs
    change (sets action).2 ≤ setBudget at hset
    change (lookups action).2 ≤ lookupBudget at hlookup
    change (chunks action).2 ≤ (sets action).2 + layout.2 +
      3 * ((layout.1.map List.length).sum * (2 * queryAccess + 5) + 6) + 3 at hchunk
    dsimp only [preparation]
    omega
  have hbudget : ∀ action, subProofConstraintCostBudget costs node queryAccess gates.1
      (sets action).1 (chunks action).1 (lookups action).1 stride ≤ budget := by
    intro action
    exact plonkPreparedConstraintCostBudget_bound costs node queryAccess equal read views action
      (instanceQueries action) (adviceQueries action) fixedQueries sigmaQueries gates.1 layout inputs tables stride
  have hlength : ∀ action, gates.1.length + (sets action).1.length + (chunks action).1.length +
      5 * (lookups action).1.length + 2 ≤ gates.1.length + 23 := by
    intro action
    have hc := permutationQueryChunksCosted_length_le (instanceQueries action) (adviceQueries action)
      fixedQueries sigmaQueries (sets action) layout
    have hp := plonkPermutationSetsCosted_length equal read views action
    have hl := plonkLookupInputsCosted_length equal read views action inputs tables
    change (chunks action).1.length ≤ (sets action).1.length at hc
    change (sets action).1.length = 3 at hp
    change (lookups action).1.length = 3 at hl
    omega
  have h := allConstraintsCosted_cost_le costs node queryAccess preparation budget (gates.1.length + 23)
    fixedQueries adviceQueries instanceQueries gates.1 sets chunks lookups beta gamma x delta theta
    stride l0 lLast lBlind hf ha hi hsets hchunks hlookups hprepare hbudget hlength
    (hbeta.trans haccess) (hgamma.trans haccess) (hx.trans haccess) (hdelta.trans haccess)
    (htheta.trans haccess) (hl0.trans haccess) (hlLast.trans haccess) (hlBlind.trans haccess)
  exact Nat.add_le_add_right (Nat.add_le_add_left h gates.2) 1

end Zcash.Snark.ZeroKnowledge
