import Zcash.Snark.ZeroKnowledge.GateActivationCoverage
import Zcash.Snark.ZeroKnowledge.SourceGateCompleteness
import Zcash.Snark.ZeroKnowledge.InactiveSelectorReplacement
import Zcash.Circuits.Integration.TopLevelGates

/-!
# Source constraints imply compiled gate equations

Original operation constraints and a complete source activation certificate imply
every compressed gate equation. Query-layout interpretation then transfers the
result through the actual compiler to the verifier expressions. Inactive selectors
are handled by their proved root polynomials, including zero values.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- The canonical compiler environment reads its exact dense fixed row on the domain. -/
theorem topLevel_environment_fixed_nat {p : ℕ} [Fact p.Prime]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit (F p) Config PublicInput) (assignment : ProofAssignment (F p))
    (column : Column .fixed) (row : ℕ) (hrow : row < top.n) :
    (top.environment assignment).fixed column (row : ℤ) =
      (top.fixedRows.getD column.index []).getD row 0 := by
  rw [TopLevelCircuit.environment_fixed]
  change (top.fixedRows.getD column.index []).getD ((row : ℤ).natMod top.n) 0 = _
  simp only [Int.natMod]
  rw [Int.emod_eq_of_lt (Nat.cast_nonneg row) (by exact_mod_cast hrow), Int.toNat_natCast]

/-- Source constraints imply every compressed gate when activation coverage is complete. -/
theorem topLevel_substitutedGate_zero_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (hlabels : (top.constraintSystem.gates.map sourceGateLabel).Nodup)
    (hcoverage : gateActivationCoverageCheck (top.constraintSystem.gates.map sourceGateLabel)
      top.selectorActivations (sourceGateActivationLabels top.placement top.operations 0) = true)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (gate : Gate Fp) (hgate : gate ∈ top.constraintSystem.gates)
    (constraint : Constraint Fp) (hconstraint : constraint ∈ gate.constraints)
    (hdegree : sourceSelectorGated gate.selector constraint.poly = true)
    (row : ℕ) (hrow : row < top.n) :
    (substSelectorMap top.selectorMap.lookup constraint.poly).eval
      (Query.eval (top.environment assignment) (fun _ => 0) row) = 0 := by
  rw [substSelectorMap_eval]
  apply sourceSelectorGated_eval_zero gate.selector _ constraint.poly hdegree
  by_cases hactive : (gate.selector.index, row) ∈ top.selectorActivations
  · right
    obtain ⟨enabled, henabled, hsame, hplaced⟩ :=
      topLevel_gate_enabled_of_coverage top hlabels hcoverage gate hgate row hactive
    have hsatisfied := (CircuitConstraintFamily.gate_constraints_iff_enabledGates
      top.placement (top.environment assignment) top.operations 0).mp
      (FullCircuitSatisfaction.of_constraints hconstraints).gates
    have h := List.forall_iff_forall_mem.mp hsatisfied enabled henabled
    have hconstraint' : constraint ∈ enabled.gate.constraints := hsame ▸ hconstraint
    have hzero := List.forall_iff_forall_mem.mp h constraint hconstraint'
    rw [hsame, hplaced] at hzero
    rw [Expression.eval_enabledGateValuation_eq_queryEval
      (substValuation top.selectorMap.lookup
        (Query.eval (top.environment assignment) (fun _ => 0) row))
      (top.environment assignment) gate.selector row constraint.poly
      (by intro column rotation; rfl) (by intro column rotation; rfl)
      (by intro column rotation; rfl)]
    exact hzero
  · left
    cases hlookup : top.selectorMap.lookup gate.selector.index with
    | none => simp [substValuation, hlookup, Query.eval]
    | some compressed =>
      simp only [substValuation, hlookup]
      apply topLevel_selReplacement_zero_of_inactive top gate.selector.index compressed
        hlookup row hrow _ ?_ hactive
      simpa only [Query.eval, add_zero] using
        topLevel_environment_fixed_nat top assignment ⟨compressed.packedCol⟩ row hrow

/-- The final verifier expressions inherit source completeness through the exact query compiler. -/
theorem topLevel_verifierGates_zero_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (hlabels : (top.constraintSystem.gates.map sourceGateLabel).Nodup)
    (hcoverage : gateActivationCoverageCheck (top.constraintSystem.gates.map sourceGateLabel)
      top.selectorActivations (sourceGateActivationLabels top.placement top.operations 0) = true)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (hdegree : ∀ gate ∈ top.constraintSystem.gates, ∀ constraint ∈ gate.constraints,
      sourceSelectorGated gate.selector constraint.poly = true)
    (row : ℕ) (hrow : row < top.n) (fixed advice instanceFeed : ℕ → Fp)
    (hinterprets : Interprets top.gateQueryState fixed advice instanceFeed
      (Query.eval (top.environment assignment) (fun _ => 0) row)) :
    ∀ expression ∈ top.verifierCS.gates, expression.eval fixed advice instanceFeed = 0 := by
  intro expression hexpression
  obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hexpression
  have hsource : index < (flatGates top.constraintSystem).length := by
    simpa only [TopLevelCircuit.verifierCS_gates_length] using hindex
  rw [top.verifierCS_gates_eval fixed advice instanceFeed _
    (TopLevelConstraintBounds.gateSelectorsCovered (top := top)) hinterprets index hindex hsource]
  have hmember := List.getElem_mem hsource
  obtain ⟨gate, hgate, hconstraintMember⟩ := List.mem_flatMap.mp hmember
  obtain ⟨constraint, hconstraint, hequal⟩ := List.mem_map.mp hconstraintMember
  have h := topLevel_substitutedGate_zero_of_constraints top assignment hlabels hcoverage
    hconstraints gate hgate constraint hconstraint (hdegree gate hgate constraint hconstraint) row hrow
  rw [substSelectorMap_eval] at h
  exact hequal ▸ h

end Zcash.Snark.ZeroKnowledge
