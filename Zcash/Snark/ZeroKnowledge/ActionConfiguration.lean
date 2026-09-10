import Zcash.Circuits.Action.PlannerTrace
import Zcash.Snark.ZeroKnowledge.PlonkQueryLayout
import Zcash.Snark.Keygen.Pipeline

/-!
# Action configuration used by the reference prover

These facts come from the actual Action configure program and the proved compiler
degree and placement metadata. Advice and instance query order, the permutation
columns, and all dimensions except the compressed fixed-query count are derived
without evaluating the dense circuit rows or importing a captured-key equality.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action

/-- The actual Action configure program creates three lookup arguments. -/
theorem actionCircuit_lookupCount_eq : actionCircuit.lookupCount = 3 := by
  rw [TopLevelCircuit.lookupCount, Internal.actionCircuit_eq_impl]
  change (((Circuit.configure Specs.Sinsemilla.orchardGenerators).delta {}).lookups).length = 3
  have h := congrArg List.length
    (Circuit.configure_lookupInputLengths Specs.Sinsemilla.orchardGenerators)
  simpa only [List.length_map, List.length_cons, List.length_nil] using h

/-- Action's proved degree nine gives permutation chunks of width seven. -/
theorem actionCircuit_chunkLen_eq : actionCircuit.chunkLen = 7 := by
  rw [TopLevelCircuit.chunkLen, ConstraintSystem.chunkLen,
    actionCircuit.constraintSystem_csDegree, actionCircuit_constraintDegree_eq]

/-- Fifteen Action permutation columns occupy three compiler chunks. -/
theorem actionCircuit_permutationSetCount_eq : actionCircuit.permutationSetCount = 3 := by
  rw [TopLevelCircuit.permutationSetCount, actionCircuit_permutationColumnCount_eq,
    actionCircuit_chunkLen_eq]

/-- The compiled Action constraint degree requires eight quotient pieces. -/
theorem actionCircuit_quotientPieceCount_eq : actionCircuit.quotientPieceCount = 8 := by
  rw [TopLevelCircuit.quotientPieceCount, actionCircuit.constraintSystem_csDegree,
    actionCircuit_constraintDegree_eq]

/-- The actual Action instance-query order is the reference protocol's single query. -/
theorem actionCircuit_instanceQueryLayout_eq : actionCircuit.instanceQueryLayout = [(0, 0)] := by
  rw [TopLevelCircuit.instanceQueryLayout_eq_constraintSystem, Internal.actionCircuit_eq_impl]
  unfold TopLevelCircuit.constraintSystem TopLevelCompilation.constraintSystem
  simp only [Internal.actionCircuitImpl, Circuit.circuit]
  configure_norm

set_option maxRecDepth 10000 in
/-- All twenty-five reference advice queries are exactly the Action configure order. -/
theorem actionCircuit_adviceQueryLayout_eq :
    actionCircuit.adviceQueryLayout = List.ofFn (fun j : Fin 25 =>
      ((plonkAdviceQueryOrder j).1.val, plonkQueryRotation (plonkAdviceQueryOrder j).2.castSucc)) := by
  rw [TopLevelCircuit.adviceQueryLayout_eq_constraintSystem, Internal.actionCircuit_eq_impl]
  unfold TopLevelCircuit.constraintSystem TopLevelCompilation.constraintSystem
  simp only [Internal.actionCircuitImpl, Circuit.circuit]
  simp only [plonkAdviceQueryOrder, plonkQueryRotation, List.ofFn_succ, List.ofFn_zero]
  configure_norm

set_option maxRecDepth 10000 in
/-- The fourteen fixed queries registered before selector compression, in actual configure order. -/
theorem actionCircuit_recordedFixedQueries_eq :
    (recordedQueries actionCircuit.constraintSystem).fixed =
      #[(3, 0), (0, 0), (11, 0), (4, 0), (5, 0), (6, 0), (7, 0),
        (8, 0), (9, 0), (10, 0), (12, 0), (1, 0), (2, 0), (13, 0)] := by
  rw [Internal.actionCircuit_eq_impl]
  unfold recordedQueries TopLevelCircuit.constraintSystem TopLevelCompilation.constraintSystem
  simp only [Internal.actionCircuitImpl, Circuit.circuit]
  configure_norm

/-- Fixed-column registration depends only on the incoming fixed-column list, allowing other
query-state fields to be discarded. -/
private theorem registerFixed_fold_congr (columns : List ℕ) (left right : QueryState)
    (hfixed : left.fixed = right.fixed) :
    (columns.foldl QueryState.registerFixed left).fixed =
      (columns.foldl QueryState.registerFixed right).fixed := by
  induction columns generalizing left right with
  | nil => exact hfixed
  | cons column rest ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [QueryState.registerFixed, hfixed]
      split
      · exact hfixed
      · rfl

/-- Fifteen packed selector columns determine the full fixed-query order without dense row evaluation. -/
theorem actionCircuit_fixedQueryLayout_of_selectorCount
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    actionCircuit.fixedQueryLayout =
      List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, (0 : ℤ))) := by
  rw [TopLevelCircuit.fixedQueryLayout_eq_gateQueryState]
  unfold TopLevelCircuit.gateQueryState queryWalkInit
  rw [hpacked, actionCircuit_numFixedColumns_eq]
  have h := registerFixed_fold_congr ((List.range 15).map (14 + ·))
    (recordedQueries actionCircuit.constraintSystem)
    { fixed := #[(3, 0), (0, 0), (11, 0), (4, 0), (5, 0), (6, 0), (7, 0),
      (8, 0), (9, 0), (10, 0), (12, 0), (1, 0), (2, 0), (13, 0)] }
    actionCircuit_recordedFixedQueries_eq
  rw [List.foldl_map] at h
  rw [h]
  decide +kernel

set_option maxRecDepth 10000 in
/-- The compiler's permutation order is the instance, ten advice columns, and four fixed columns. -/
theorem actionCircuit_permutationColumns_eq :
    actionCircuit.permutationColumns =
      [⟨.instance, 0⟩] ++ (List.range 10).map (fun c => ⟨.advice, c⟩) ++
        [⟨.fixed, 3⟩, ⟨.fixed, 8⟩, ⟨.fixed, 9⟩, ⟨.fixed, 10⟩] := by
  rw [TopLevelCircuit.permutationColumns, Internal.actionCircuit_eq_impl]
  unfold TopLevelCircuit.constraintSystem TopLevelCompilation.constraintSystem
  simp only [Internal.actionCircuitImpl, Circuit.circuit]
  configure_norm

/-- After compression, only the fixed-query count remains to identify the complete Action shape. -/
theorem actionCircuit_shape_of_fixedQueryCount (actions k : ℕ) (hk : k = 11)
    (hfixed : actionCircuit.fixedQueryCount = 29) :
    actionCircuit.shape = (plonkProofShape actions k).toCircuitShape := by
  cases hk
  simp only [TopLevelCircuit.shape, plonkProofShape, FixtureMax.shape,
    actionCircuit_domainExponent_eq, TopLevelCircuit.adviceColumnCount,
    actionCircuit_numAdviceColumns_eq, actionCircuit_lookupCount_eq,
    actionCircuit_permutationSetCount_eq, actionCircuit_permutationColumnCount_eq,
    actionCircuit_quotientPieceCount_eq, actionCircuit_numInstanceColumns_eq,
    TopLevelCircuit.instanceQueryCount, actionCircuit_instanceQueryLayout_eq,
    TopLevelCircuit.adviceQueryCount, actionCircuit_adviceQueryLayout_eq,
    List.length_cons, List.length_nil, List.length_ofFn, hfixed]

/-- The remaining compression count supplies the reference shape; all other dimensions are proved. -/
theorem actionCircuit_referenceShape (actions k : ℕ) (hk : k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    actionCircuit.shape = (plonkProofShape actions k).toCircuitShape := by
  apply actionCircuit_shape_of_fixedQueryCount actions k hk
  rw [TopLevelCircuit.fixedQueryCount, actionCircuit_fixedQueryLayout_of_selectorCount hpacked,
    List.length_ofFn]

end Zcash.Snark.ZeroKnowledge
