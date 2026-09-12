import Zcash.Snark.ZeroKnowledge.ActionConfiguration

/-!
# The converse selector law for original Action gates

A structural degree checker certifies homogeneous dependence on the full owner
selector and rejects foreign selector handles. Its semantic theorem covers every
field valuation, including a zero selector. All configured Action constraints
pass the positive-degree check directly from the original configure program.

This supplies the converse gate-scaling law needed by constructor completeness.
Relating every source activation, including gates that share a selector, to the
compiled row valuation remains a separate source-routing obligation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- A source expression's homogeneous degree in one selector; foreign selectors are rejected. -/
def sourceSelectorDegree {F : Type} (owner : Selector) : Expression F Query → Option ℕ
  | .const _ => some 0
  | .var (.selector selector) => if selector = owner then some 1 else none
  | .var _ => some 0
  | .add left right => do
      let a ← sourceSelectorDegree owner left
      let b ← sourceSelectorDegree owner right
      if a = b then some a else none
  | .mul left right => do
      let a ← sourceSelectorDegree owner left
      let b ← sourceSelectorDegree owner right
      some (a + b)

/-- A checked positive selector degree excludes constant terms and foreign selector dependencies. -/
def sourceSelectorGated {F : Type} (owner : Selector) (expression : Expression F Query) : Bool :=
  match sourceSelectorDegree owner expression with
  | some degree => degree != 0
  | none => false

/-- Scaling the owner selector scales a checked homogeneous polynomial by exactly that degree. -/
theorem sourceSelectorDegree_eval {F : Type} [Field F]
    (owner : Selector) (valuation : Query → F) (expression : Expression F Query)
    (degree : ℕ) (hdegree : sourceSelectorDegree owner expression = some degree) :
    expression.eval valuation = valuation (.selector owner) ^ degree *
      expression.eval (Expression.enabledGateValuation owner valuation) := by
  induction expression generalizing degree with
  | const value =>
      simp only [sourceSelectorDegree, Option.some.injEq] at hdegree
      subst degree
      simp [Expression.eval]
  | var query =>
      cases query with
      | selector selector =>
          simp only [sourceSelectorDegree] at hdegree
          split at hdegree
          next howner =>
            subst selector
            have hd := Option.some.inj hdegree
            subst degree
            simp [Expression.eval, Expression.enabledGateValuation]
          next => cases hdegree
      | fixed column rotation =>
          have hd := Option.some.inj hdegree
          subst degree
          simp [Expression.eval, Expression.enabledGateValuation]
      | advice column rotation =>
          have hd := Option.some.inj hdegree
          subst degree
          simp [Expression.eval, Expression.enabledGateValuation]
      | «instance» column rotation =>
          have hd := Option.some.inj hdegree
          subst degree
          simp [Expression.eval, Expression.enabledGateValuation]
  | add left right ihLeft ihRight =>
      cases hl : sourceSelectorDegree owner left with
      | none => simp [sourceSelectorDegree, hl] at hdegree
      | some a =>
          cases hr : sourceSelectorDegree owner right with
          | none => simp [sourceSelectorDegree, hl, hr] at hdegree
          | some b =>
              by_cases hab : a = b
              · subst b
                have hd : a = degree := by
                  simpa [sourceSelectorDegree, hl, hr] using hdegree
                subst degree
                simp only [Expression.eval]
                rw [ihLeft a hl, ihRight a hr, mul_add]
              · simp [sourceSelectorDegree, hl, hr, hab] at hdegree
  | mul left right ihLeft ihRight =>
      cases hl : sourceSelectorDegree owner left with
      | none => simp [sourceSelectorDegree, hl] at hdegree
      | some a =>
          cases hr : sourceSelectorDegree owner right with
          | none => simp [sourceSelectorDegree, hl, hr] at hdegree
          | some b =>
              have hd : a + b = degree := by
                simpa [sourceSelectorDegree, hl, hr] using hdegree
              subst degree
              simp only [Expression.eval]
              rw [ihLeft a hl, ihRight b hr, pow_add]
              ring

/-- A positively gated expression vanishes when inactive or when its enabled equation holds. -/
theorem sourceSelectorGated_eval_zero {F : Type} [Field F]
    (owner : Selector) (valuation : Query → F) (expression : Expression F Query)
    (hcheck : sourceSelectorGated owner expression = true)
    (hzero : valuation (.selector owner) = 0 ∨
      expression.eval (Expression.enabledGateValuation owner valuation) = 0) :
    expression.eval valuation = 0 := by
  cases hd : sourceSelectorDegree owner expression with
  | none => simp [sourceSelectorGated, hd] at hcheck
  | some degree =>
      have hpositive : degree ≠ 0 := by simpa [sourceSelectorGated, hd] using hcheck
      rw [sourceSelectorDegree_eval owner valuation expression degree hd]
      rcases hzero with hinactive | henabled
      · rw [hinactive, zero_pow hpositive, zero_mul]
      · rw [henabled, mul_zero]

set_option maxRecDepth 10000 in
/-- Every configured Action gate has positive homogeneous degree in its own selector. -/
theorem actionCircuit_sourceGateHomogeneous :
    Zcash.Circuits.Action.actionCircuit.constraintSystem.gates.all (fun gate =>
      gate.constraints.all (fun constraint => sourceSelectorGated gate.selector constraint.poly)) = true := by
  rw [Zcash.Circuits.Action.Internal.actionCircuit_eq_impl]
  rfl

/-- Every actual Action gate obeys the converse selector law, including a zero selector value. -/
theorem actionCircuit_sourceGate_complete
    (gate : Gate Zcash.Arithmetic.Fp)
    (hgate : gate ∈ Zcash.Circuits.Action.actionCircuit.constraintSystem.gates)
    (constraint : Constraint Zcash.Arithmetic.Fp) (hconstraint : constraint ∈ gate.constraints)
    (valuation : Query → Zcash.Arithmetic.Fp)
    (hzero : valuation (.selector gate.selector) = 0 ∨
      constraint.poly.eval (Expression.enabledGateValuation gate.selector valuation) = 0) :
    constraint.poly.eval valuation = 0 :=
  sourceSelectorGated_eval_zero gate.selector valuation constraint.poly
    (List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceGateHomogeneous gate hgate)
      constraint hconstraint) hzero

end Zcash.Snark.ZeroKnowledge
