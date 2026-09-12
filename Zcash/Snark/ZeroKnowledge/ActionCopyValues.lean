import Zcash.Snark.ZeroKnowledge.PlonkCopyValues
import Zcash.Snark.ZeroKnowledge.ActionQueryValuation
import Zcash.Snark.ZeroKnowledge.CopySourceCompleteness

/-!
# Action copy equations in the prover's packed cells

The finite query check retains column kind, source column, and zero rotation for
every permutation reference. Semantic interpretation and the ordered compiler
copy stream then imply the actual prover's cell equalities.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Halo2.Layout Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- The original unrotated query represented by a compiler permutation column. -/
def sourceCopyQuery : ColRef → Query
  | .advice column => .advice ⟨column⟩ 0
  | .fixed column => .fixed ⟨column⟩ 0
  | .instance column => .instance ⟨column⟩ 0

/-- Check column kind, column index, and zero rotation against the actual query array. -/
def copyReferenceResolves (state : QueryState) : ColumnRef → ColRef → Bool
  | .advice index, .advice column => state.advice[index]? == some (column, 0)
  | .fixed index, .fixed column => state.fixed[index]? == some (column, 0)
  | .instance index, .instance column => state.inst[index]? == some (column, 0)
  | _, _ => false

/-- A successful query check preserves the semantic value for every interpreted feed. -/
theorem copyReferenceResolves_value {F : Type} [Field F]
    (state : QueryState) (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (hinterprets : Interprets state fixed advice instanceFeed valuation)
    (reference : ColumnRef) (column : ColRef)
    (hcheck : copyReferenceResolves state reference column = true) :
    reference.resolve instanceFeed advice fixed = valuation (sourceCopyQuery column) := by
  cases reference <;> cases column <;>
    simp only [copyReferenceResolves, beq_iff_eq, Bool.false_eq_true] at hcheck
  all_goals first
    | contradiction
    | exact hinterprets.advice _ _ _ hcheck
    | exact hinterprets.fixed _ _ _ hcheck
    | exact hinterprets.inst _ _ _ hcheck

/-- A source copy query is exactly its absolute compiler-environment read. -/
theorem sourceCopyQuery_eval (environment : Environment Fp) (selectors : ℕ → Fp)
    (columns : List ColRef) (column row : ℕ) :
    Query.eval environment selectors row (sourceCopyQuery (columns.getD column (.advice 0))) =
      sourceCopyValue columns environment (column, row) := by
  unfold sourceCopyValue
  generalize columns.getD column (.advice 0) = reference
  cases reference <;> simp [sourceCopyQuery, Query.eval, ColRef.toAny]
  all_goals rfl

/-- All fifteen source permutation columns, in the actual compiler order. -/
theorem actionCircuit_permCols_eq :
    Keygen.permColsOf actionCircuit.constraintSystem =
      [.instance 0, .advice 0, .advice 1, .advice 2, .advice 3, .advice 4, .advice 5,
        .advice 6, .advice 7, .advice 8, .advice 9, .fixed 3, .fixed 8, .fixed 9, .fixed 10] := by
  unfold Keygen.permColsOf
  change actionCircuit.permutationColumns.map _ = _
  rw [actionCircuit_permutationColumns_eq]
  rfl

/-- Every reference in the three actual chunks resolves to its corresponding source column. -/
theorem actionCircuit_copyReferences_resolve :
    ∀ chunk : Fin 3, ∀ column : Fin ((actionReferencePermutationChunks.getD chunk.val []).length),
      copyReferenceResolves actionCircuit.gateQueryState
        ((actionReferencePermutationChunks.getD chunk.val []).getD column.val (.advice 0, 0)).1
        ((Keygen.permColsOf actionCircuit.constraintSystem).getD (chunk.val * 7 + column.val) (.advice 0)) = true := by
  have hinst : actionCircuit.gateQueryState.inst = #[(0, (0 : ℤ))] := by
    rw [← actionCircuit.pinnedQueryState_eq_gateQueryState]
    change actionCircuit.instanceQueryLayout.toArray = _
    rw [actionCircuit_instanceQueryLayout_eq]
  unfold copyReferenceResolves
  rw [actionCircuit_permCols_eq, actionCircuit_gateQueryState_advice,
    actionCircuit_gateQueryState_fixed actionCircuit_newFixedCols_eq_fifteen, hinst]
  decide +kernel

/-- Each actual prover cell reads the original compiler endpoint, for every application witness. -/
theorem actionCopyCellPair_sourceValue {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (action : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (hchunks : chunks = actionReferencePermutationChunks) (cell : PlonkCopyCell chunks) :
    (plonkCopyCellPair (actionPublicPolynomials inputs)
      (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action chunks cell).1 =
    sourceCopyValue (Keygen.permColsOf actionCircuit.constraintSystem)
      (actionCircuit.environment (actionWitnessAssignment (inputs action) (witnesses action)))
      (plonkCopyCellRaw cell) := by
  subst chunks
  rw [plonkCopyCellPair_value]
  have hinterprets := actionWitnessRowFeeds_interpret inputs witnesses action
    (cell.2.1.castLE (by decide)) (cell.2.1.isLt.trans (by decide : 2042 < 2047))
  have hvalue := copyReferenceResolves_value _ _ _ _ _ hinterprets
    (plonkCopyCellEntry cell).1
    ((Keygen.permColsOf actionCircuit.constraintSystem).getD (plonkCopyCellRaw cell).1 (.advice 0))
    (actionCircuit_copyReferences_resolve cell.1 cell.2.2)
  exact hvalue.trans (sourceCopyQuery_eval _ _ _ _ _)

/-- Original Action constraints imply every packed permutation-cell equation used by the prover. -/
theorem actionWitnessRows_copies_of_constraints {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (hconstraints : ∀ action : Fin actions, Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment (inputs action) (witnesses action)))
      actionCircuit.operations 0)
    (chunks : List (List (ColumnRef × ℕ))) (hchunks : chunks = actionReferencePermutationChunks)
    (hwidth : plonkCopyChunkWidths chunks) :
    ∀ action : Fin actions, ∀ pair ∈ plonkKeygenCopies actionCircuit
      actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) chunks hwidth,
      (plonkCopyCellPair (actionPublicPolynomials inputs)
        (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action chunks pair.1).1 =
      (plonkCopyCellPair (actionPublicPolynomials inputs)
        (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action chunks pair.2).1 := by
  intro action pair hpair
  rw [actionCopyCellPair_sourceValue inputs witnesses action chunks hchunks pair.1,
    actionCopyCellPair_sourceValue inputs witnesses action chunks hchunks pair.2]
  have hraw : ((plonkCopyCellRaw pair.1).1, (plonkCopyCellRaw pair.1).2,
      (plonkCopyCellRaw pair.2).1, (plonkCopyCellRaw pair.2).2) ∈ plonkKeygenCopyRaw actionCircuit := by
    rw [← plonkKeygenCopies_encode actionCircuit actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) chunks hwidth]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  exact topLevel_copyValues_of_constraints actionCircuit
    (actionWitnessAssignment (inputs action) (witnesses action)) (hconstraints action) _ hraw

end Zcash.Snark.ZeroKnowledge
