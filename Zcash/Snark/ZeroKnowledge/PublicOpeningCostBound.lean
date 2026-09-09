import Zcash.Snark.ZeroKnowledge.PublicOpeningCost

/-!
# Complete public-opening cost bound

The bound substitutes the proved budgets for every preparation stage. Its only
access premises price the actual row, generator, commitment, and observation
readers. Challenge and supplied scalar costs remain explicit. All bounds are
structural and apply to the same counted algorithm as its erasure theorem.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Reading a materialized node list preserves its size bound, including the empty fallback. -/
theorem openingNodeList_getD_length_le {α : Type*} (bound : ℕ) (lists : List (List α))
    (h : ∀ values ∈ lists, values.length ≤ bound) (index : ℕ) :
    (lists.getD index []).length ≤ bound := by
  induction lists generalizing index with
  | nil => change 0 ≤ bound; exact Nat.zero_le _
  | cons first rest ih =>
    cases index with
    | zero => exact h first (List.mem_cons_self)
    | succ index => exact ih (fun values hmem => h values (List.mem_cons_of_mem _ hmem)) index

/-- Every assembled opening entry retains the supplied node-size bounds and a stored scalar read. -/
theorem openingEvaluationSetsCosted_entry_bounds (read : ℕ) (points nodes : List (List Fp) × ℕ)
    (values : List Fp × ℕ)
    (hpoints : ∀ pointSet ∈ points.1, pointSet.length ≤ 3)
    (hnodes : ∀ nodeSet ∈ nodes.1, nodeSet.length ≤ 3)
    (entry : List Fp × List Fp × (Fp × ℕ))
    (hentry : entry ∈ (openingEvaluationSetsCosted read points nodes values).1) :
    entry.1.length ≤ 3 ∧ entry.2.1.length ≤ 3 ∧ entry.2.2.2 ≤ 1 := by
  simp only [openingEvaluationSetsCosted, ofFnCosted_result, List.mem_ofFn] at hentry
  obtain ⟨index, rfl⟩ := hentry
  simp only [openingSetEntryCosted_result]
  exact ⟨openingNodeList_getD_length_le 3 points.1 hpoints index.val,
    openingNodeList_getD_length_le 3 nodes.1 hnodes index.val, le_rfl⟩

/-- Explicit polynomial budget for complete public multi-opening, with all access prices retained. -/
def plonkPublicOpeningCostBudget (costs : FieldOperationCosts)
    (groupAdd groupScale equal read omegaAccess actions columns rowRead generatorRead wAccess
      pointRead observationRead xAccess x1Access x2Access x4Access qAccess hAccess rAccess firstAccess : ℕ) : ℕ :=
  let pointAccess := publicOpeningPointAccessBudget costs groupAdd groupScale equal omegaAccess actions
    rowRead generatorRead wAccess pointRead xAccess
  let firstCommitment := actions * actions + actions * (4 * pointAccess + 40) + 50 * pointAccess + 1200 +
    (4 * actions + 46) * (x1Access + groupScale + groupAdd + 3) + 3
  let privateCommitment := actions * actions + 35 * actions + 9 * actions *
    (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + pointRead + 13 +
      x1Access + groupScale + groupAdd + 2) + 4
  let commitments := firstCommitment + 4 * (privateCommitment + 1) + 19
  let claimAccess := publicOpeningClaimAccessBudget costs equal read omegaAccess actions columns
    rowRead observationRead xAccess hAccess rAccess
  let firstNode := actions * actions + actions * (4 * claimAccess + 40) + 50 * claimAccess + 1200 +
    (4 * actions + 46) * (x1Access + costs.multiply + costs.add + 3) + 3
  let privateValue := privateOpeningEvaluationCostBudget costs equal read actions columns observationRead x1Access
  let nodes := firstNode + 4 * (3 * (privateValue + 1) + 19) + 20
  let values := firstAccess + 4 * (privateValue + 1) + 19
  let pointSets := 5 * (3 * (xAccess + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 14) + 19) + 26
  let sets := pointSets + nodes + values + 5 * (30 + 3 * read + 8) + 27
  let initial := 5 * (multiopenSetEvalCostBudget costs read 3 3 qAccess 1 +
    x2Access + costs.multiply + costs.add + 4) + 7
  let combination := pointRead + 3 + initial + 10 +
    5 * (2 * x4Access + 1 + 1 + groupScale + groupAdd + costs.multiply + costs.add + 2) + 5
  commitments + sets + 16 + 16 + combination + 1

/-- The entire public opening, including all polynomial and group preparation, fits the explicit budget. -/
theorem plonkPublicOpeningCosted_cost_le (costs : FieldOperationCosts)
    (groupAdd groupScale equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (points : Fin (22 * actions + 10) → G × ℕ) (views : List (Fin 5 → Fp × ℕ))
    (x x1 x2 x4 q hEval rEval firstGroup : Fp × ℕ)
    (rowRead generatorRead pointRead observationRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hgenerators : ∀ index, (generators index).2 ≤ generatorRead)
    (hpoints : ∀ index, (points index).2 ≤ pointRead)
    (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ observationRead) :
    (plonkPublicOpeningCosted costs groupAdd groupScale equal read omegaAccess
      instances fixed sigma generators W points views x x1 x2 x4 q hEval rEval firstGroup).2 ≤
      plonkPublicOpeningCostBudget costs groupAdd groupScale equal read omegaAccess actions views.length
        rowRead generatorRead W.2 pointRead observationRead x.2 x1.2 x2.2 x4.2 q.2 hEval.2 rEval.2 firstGroup.2 := by
  let commitments := openingCommitmentVectorCosted costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x x1 points
  let nodes := openingNodeValuesCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval
  let values := openingGroupValuesCosted (actions := actions) costs equal read views x1 firstGroup
  let pointSets := openingPointSetsCosted costs (omegaOf 11, omegaAccess) x
  let sets := openingEvaluationSetsCosted read pointSets nodes values
  let initial := multiopenEvalCosted costs read x2 q sets.1
  let pointEntries := mapListCosted (fun point => ((point, 1), 2)) commitments.1
  let valueEntries := mapListCosted (fun value => ((value, 1), 2)) values.1
  let quotientPrime := plonkQuotientPrimeEntryCosted points
  have hcommitments := openingCommitmentVectorCosted_cost_le costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x x1 points rowRead generatorRead pointRead
    hinstances hfixed hsigma hgenerators hpoints
  have hnodes := openingNodeValuesCosted_cost_le costs equal read omegaAccess instances fixed sigma views
    x x1 hEval rEval rowRead observationRead hinstances hfixed hsigma hviews
  have hvalues := openingGroupValuesCosted_cost_le (actions := actions) costs equal read views x1 firstGroup
    observationRead hviews
  have hpointSets := openingPointSetsCosted_cost_le costs (omegaOf 11, omegaAccess) x
  have hcommitmentsLength : commitments.1.length = 5 :=
    openingCommitmentVectorCosted_length costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x x1 points
  have hnodesLength : nodes.1.length = 5 :=
    openingNodeValuesCosted_length costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval
  have hvaluesLength : values.1.length = 5 := openingGroupValuesCosted_length costs equal read views x1 firstGroup
  have hpointSetsLength : pointSets.1.length = 5 := openingPointSetsCosted_length costs (omegaOf 11, omegaAccess) x
  have hsets := openingEvaluationSetsCosted_cost_le read pointSets nodes values
  rw [hpointSetsLength, hnodesLength, hvaluesLength] at hsets
  have hsetsLength : sets.1.length ≤ 5 := (openingEvaluationSetsCosted_length read pointSets nodes values).le
  have hsetBounds (entry) (hentry : entry ∈ sets.1) :
      entry.1.length ≤ 3 ∧ entry.2.1.length ≤ 3 ∧ entry.2.2.2 ≤ 1 :=
    openingEvaluationSetsCosted_entry_bounds read pointSets nodes values
      (fun pointSet hmem => by
        simp only [pointSets, openingPointSetsCosted_result, List.mem_ofFn] at hmem
        obtain ⟨index, rfl⟩ := hmem
        exact (plonkOpeningPointSets_length (omegaOf 11) x.1 index).2)
      (fun nodeSet hmem => (openingNodeValuesCosted_node_lengths costs equal read omegaAccess
        instances fixed sigma views x x1 hEval rEval nodeSet hmem).2) entry hentry
  have hinitial := (multiopenEvalCosted_cost_le costs read x2 q sets.1).trans
    (multiopenEvalCostBudget_le_five costs read x2.2 q.2 1 sets.1 hsetsLength hsetBounds)
  have hpointEntries := mapListCosted_cost_le (fun point : G => ((point, 1), 2)) commitments.1 2
    (fun _ _ => le_rfl)
  have hvalueEntries := mapListCosted_cost_le (fun value : Fp => ((value, 1), 2)) values.1 2
    (fun _ _ => le_rfl)
  rw [hcommitmentsLength] at hpointEntries
  rw [hvaluesLength] at hvalueEntries
  have hpointEntriesLength : pointEntries.1.length = 5 := by
    simp only [pointEntries, mapListCosted_result, List.length_map, hcommitmentsLength]
  have hquotientPrime := plonkQuotientPrimeEntryCosted_cost_le points pointRead hpoints
  have hcombination := multiopenPointFoldCosted_cost_le costs groupAdd groupScale x4 quotientPrime
    pointEntries.1 valueEntries.1 initial 1 1
    (fun point hmem => by
      simp only [pointEntries, mapListCosted_result, List.mem_map] at hmem
      obtain ⟨_, _, rfl⟩ := hmem
      exact le_rfl)
    (fun value hmem => by
      simp only [valueEntries, mapListCosted_result, List.mem_map] at hmem
      obtain ⟨_, _, rfl⟩ := hmem
      exact le_rfl)
  rw [hpointEntriesLength] at hcombination
  dsimp only at hpointSets
  change commitments.2 + sets.2 + pointEntries.2 + valueEntries.2 +
    (multiopenPointFoldCosted costs groupAdd groupScale x4 quotientPrime pointEntries.1 valueEntries.1 initial).2 + 1 ≤ _
  dsimp only [plonkPublicOpeningCostBudget]
  change commitments.2 ≤ _ at hcommitments
  change nodes.2 ≤ _ at hnodes
  change values.2 ≤ _ at hvalues
  change pointSets.2 ≤ _ at hpointSets
  change initial.2 ≤ _ at hinitial
  change pointEntries.2 ≤ _ at hpointEntries
  change valueEntries.2 ≤ _ at hvalueEntries
  change quotientPrime.2 ≤ _ at hquotientPrime
  change sets.2 ≤ _ at hsets
  omega

end Zcash.Snark.ZeroKnowledge
