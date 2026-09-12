import Zcash.Snark.ZeroKnowledge.CompiledGateCompleteness

/-!
# Inactive compiled gates at arbitrary private row values

When the source selector is inactive, its compiled replacement vanishes in the
actual fixed columns. The proof carries this through every configured gate and
query erasure without any ordinary-query agreement or witness-validity premise.
This covers the final cyclic domain row as well as other inactive rows.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Inactive gates vanish for arbitrary private query values in the actual fixed rows. -/
theorem topLevel_substitutedGate_zero_of_inactive
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (gate : Gate Fp) (constraint : Constraint Fp)
    (hdegree : sourceSelectorGated gate.selector constraint.poly = true)
    (row : ℕ) (hrow : row < top.n) (valuation : Query → Fp)
    (hselector : ∀ selector, valuation (.selector selector) = 0)
    (hfixed : ∀ selector compressed, top.selectorMap.lookup selector = some compressed →
      valuation (.fixed ⟨compressed.packedCol⟩ 0) =
        (top.fixedRows.getD compressed.packedCol []).getD row 0)
    (hinactive : (gate.selector.index, row) ∉ top.selectorActivations) :
    constraint.poly.eval (substValuation top.selectorMap.lookup valuation) = 0 := by
  apply sourceSelectorGated_eval_zero gate.selector _ constraint.poly hdegree
  left
  cases hlookup : top.selectorMap.lookup gate.selector.index with
  | none => simpa only [substValuation, hlookup] using hselector gate.selector
  | some compressed =>
    simp only [substValuation, hlookup]
    exact topLevel_selReplacement_zero_of_inactive top gate.selector.index compressed hlookup
      row hrow valuation (hfixed gate.selector.index compressed hlookup) hinactive

/-- The complete compiled gate list vanishes on an inactive row, including cyclic boundary reads. -/
theorem topLevel_verifierGates_zero_of_inactive
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (hdegree : ∀ gate ∈ top.constraintSystem.gates, ∀ constraint ∈ gate.constraints,
      sourceSelectorGated gate.selector constraint.poly = true)
    (row : ℕ) (hrow : row < top.n) (valuation : Query → Fp)
    (hselector : ∀ selector, valuation (.selector selector) = 0)
    (hfixed : ∀ selector compressed, top.selectorMap.lookup selector = some compressed →
      valuation (.fixed ⟨compressed.packedCol⟩ 0) =
        (top.fixedRows.getD compressed.packedCol []).getD row 0)
    (hinactive : ∀ gate ∈ top.constraintSystem.gates,
      (gate.selector.index, row) ∉ top.selectorActivations)
    (fixed advice instanceFeed : ℕ → Fp)
    (hinterprets : Interprets top.gateQueryState fixed advice instanceFeed valuation) :
    ∀ expression ∈ top.verifierCS.gates, expression.eval fixed advice instanceFeed = 0 := by
  intro expression hexpression
  obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hexpression
  have hsource : index < (flatGates top.constraintSystem).length := by
    simpa only [TopLevelCircuit.verifierCS_gates_length] using hindex
  rw [top.verifierCS_gates_eval fixed advice instanceFeed valuation
    (TopLevelConstraintBounds.gateSelectorsCovered (top := top)) hinterprets index hindex hsource]
  obtain ⟨gate, hgate, hconstraintMember⟩ := List.mem_flatMap.mp (List.getElem_mem hsource)
  obtain ⟨constraint, hconstraint, hequal⟩ := List.mem_map.mp hconstraintMember
  exact hequal ▸ topLevel_substitutedGate_zero_of_inactive top gate constraint
    (hdegree gate hgate constraint hconstraint) row hrow valuation hselector hfixed (hinactive gate hgate)

end Zcash.Snark.ZeroKnowledge
