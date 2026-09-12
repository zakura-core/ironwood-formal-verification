import Zcash.Snark.ZeroKnowledge.AdvicePlacementBounds
import Zcash.Snark.ZeroKnowledge.ActionPublicData
import Zcash.Snark.ZeroKnowledge.ActionDerivedKey
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Actual Action rows in the compiled query feeds

The proved query layouts retain every column and rotation. Interpolation reads
those exact rows. Before the final domain row, the constructor's zero padding also
settles the signed previous-row read at row zero. These lemmas establish query
interpretation independently of witness validity or successful proof emission.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- The fixed query compiler retains the checked Action column order and zero rotations. -/
theorem actionGateQuery_fixed (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.fixed[index]? = some (column, rotation)) :
    ∃ h : index < 29, column = (plonkFixedQueryOrder ⟨index, h⟩).val ∧ rotation = 0 := by
  have hlist : actionCircuit.fixedQueryLayout[index]? = some (column, rotation) := by
    simpa only [TopLevelCircuit.fixedQueryLayout_eq_gateQueryState, Array.getElem?_toList] using hquery
  rw [actionCircuit_fixedQueryLayout_of_selectorCount actionCircuit_newFixedCols_eq_fifteen] at hlist
  obtain ⟨hindex, hequal⟩ := List.getElem?_eq_some_iff.mp hlist
  simp only [List.length_ofFn] at hindex
  simp only [List.getElem_ofFn] at hequal
  exact ⟨hindex, (congrArg Prod.fst hequal).symm, (congrArg Prod.snd hequal).symm⟩

/-- The advice query compiler retains the checked Action column and rotation order. -/
theorem actionGateQuery_advice (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.advice[index]? = some (column, rotation)) :
    ∃ h : index < 25, column = (plonkAdviceQueryOrder ⟨index, h⟩).1.val ∧
      rotation = plonkQueryRotation (plonkAdviceQueryOrder ⟨index, h⟩).2.castSucc := by
  rw [← actionCircuit.pinnedQueryState_eq_gateQueryState] at hquery
  have hlist : actionCircuit.adviceQueryLayout[index]? = some (column, rotation) := by
    simpa only [pinnedQueryState, List.getElem?_toArray] using hquery
  rw [actionCircuit_adviceQueryLayout_eq] at hlist
  obtain ⟨hindex, hequal⟩ := List.getElem?_eq_some_iff.mp hlist
  simp only [List.length_ofFn] at hindex
  simp only [List.getElem_ofFn] at hequal
  exact ⟨hindex, (congrArg Prod.fst hequal).symm, (congrArg Prod.snd hequal).symm⟩

/-- The instance query compiler reads only Action's declared column at the current row. -/
theorem actionGateQuery_instance (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.inst[index]? = some (column, rotation)) :
    index = 0 ∧ column = 0 ∧ rotation = 0 := by
  rw [← actionCircuit.pinnedQueryState_eq_gateQueryState] at hquery
  have hlist : actionCircuit.instanceQueryLayout[index]? = some (column, rotation) := by
    simpa only [pinnedQueryState, List.getElem?_toArray] using hquery
  rw [actionCircuit_instanceQueryLayout_eq] at hlist
  obtain ⟨hindex, hequal⟩ := List.getElem?_eq_some_iff.mp hlist
  have hi : index = 0 := by simpa using hindex
  subst index
  have hpair : (0, (0 : ℤ)) = (column, rotation) := hequal
  exact ⟨rfl, (congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

/-- The three cyclic advice queries agree with signed source rows, including row zero. -/
theorem plonkAdviceRotation_read_eq (read : ℤ → Fp)
    (hwrap : read 2047 = read (-1)) (rotation : Fin 3) (row : Fin 2048)
    (hrow : row.val < 2047) :
    read (plonkAdviceRotationRow rotation row).val =
      read ((row.val : ℤ) + plonkQueryRotation rotation.castSucc) := by
  fin_cases rotation
  · simp [plonkAdviceRotationRow, plonkAdviceRotationOffsets, plonkQueryRotation,
      Nat.mod_eq_of_lt row.isLt]
  · have hnext : row.val + 1 < 2048 := by omega
    simp [plonkAdviceRotationRow, plonkAdviceRotationOffsets, plonkQueryRotation,
      Nat.mod_eq_of_lt hnext, Nat.cast_add]
  · by_cases hzero : row.val = 0
    · change read (((row.val + 2047) % 2048 : ℕ) : ℤ) = read ((row.val : ℤ) + (-1))
      simpa only [hzero, Nat.zero_add, Nat.reduceMod, Nat.cast_ofNat, zero_add] using hwrap
    · have hprevious : (row.val + 2047) % 2048 = row.val - 1 := by omega
      have hcast : ((row.val - 1 : ℕ) : ℤ) = (row.val : ℤ) + (-1) := by omega
      change read (((row.val + 2047) % 2048 : ℕ) : ℤ) = read ((row.val : ℤ) + (-1))
      rw [hprevious, hcast]

/-- On all usable rows, the reference feeds interpret the actual generated Action environment. -/
theorem actionWitnessRowFeeds_interpret_of_wrap {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (action : Fin actions) (row : Fin 2048) (hrow : row.val < 2047)
    (hwrap : ∀ column : Column .advice,
      (actionWitnessAssignment (inputs action) (witnesses action)).advice column 2047 =
        (actionWitnessAssignment (inputs action) (witnesses action)).advice column (-1)) :
    Interprets actionCircuit.gateQueryState
      (plonkFixedRowValues (actionPublicPolynomials inputs) row)
      (plonkAdviceRowValues (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action row)
      (plonkInstanceRowValues (actionPublicPolynomials inputs) action row)
      (Query.eval (actionCircuit.environment
        (actionWitnessAssignment (inputs action) (witnesses action))) (fun _ => 0) row.val) := by
  constructor
  · intro index column rotation hquery
    obtain ⟨hindex, rfl, rfl⟩ := actionGateQuery_advice index column rotation hquery
    simp only [plonkAdviceRowValues, finFn, dif_pos hindex,
      plonkUnmaskedAdviceRows_eval, actionWitnessRowBundle, actionWitnessRows,
      Query.eval, TopLevelCircuit.environment_advice]
    exact plonkAdviceRotation_read_eq _ (hwrap _) _ row hrow
  · intro index column rotation hquery
    obtain ⟨hindex, rfl, rfl⟩ := actionGateQuery_fixed index column rotation hquery
    simp only [actionPublicPolynomials, plonkKeygenPublicPolynomials,
      plonkPublicPolynomialsFromRows_fixedRowValues, finFn, dif_pos hindex,
      plonkKeygenFixedRows, Query.eval, add_zero, TopLevelCircuit.environment_fixed]
    change _ = (actionCircuit.fixedRows.getD (plonkFixedQueryOrder ⟨index, hindex⟩).val []).getD
      ((row.val : ℤ).natMod actionCircuit.n) 0
    have hn : actionCircuit.n = 2048 := by
      rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
      decide
    rw [hn, Int.natMod, Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast row.isLt),
      Int.toNat_natCast]
  · intro index column rotation hquery
    obtain ⟨rfl, rfl, rfl⟩ := actionGateQuery_instance index column rotation hquery
    simp only [plonkInstanceRowValues, finFn, dif_pos (by decide : 0 < 1),
      actionPublicPolynomials_instances_eval, Query.eval, add_zero, TopLevelCircuit.environment_inst]
    change _ = (initialPublicWitnessAssignment actionCircuit (inputs action)).inst ⟨0⟩ row.val
    rw [initialPublicWitnessAssignment_inst, actionCircuit_publicInputRows_zero]

/-- The actual constructor discharges the row-zero wraparound premise for every witness. -/
theorem actionWitnessRowFeeds_interpret {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (action : Fin actions) (row : Fin 2048) (hrow : row.val < 2047) :
    Interprets actionCircuit.gateQueryState
      (plonkFixedRowValues (actionPublicPolynomials inputs) row)
      (plonkAdviceRowValues (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action row)
      (plonkInstanceRowValues (actionPublicPolynomials inputs) action row)
      (Query.eval (actionCircuit.environment
        (actionWitnessAssignment (inputs action) (witnesses action))) (fun _ => 0) row.val) := by
  apply actionWitnessRowFeeds_interpret_of_wrap inputs witnesses action row hrow
  intro column
  rw [actionWitnessAssignment_advice_zero_of_outside _ _ column 2047 (by omega),
    actionWitnessAssignment_advice_zero_of_outside _ _ column (-1) (by omega)]

end Zcash.Snark.ZeroKnowledge
