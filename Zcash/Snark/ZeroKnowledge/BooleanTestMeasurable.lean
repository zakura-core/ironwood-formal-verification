import Zcash.Snark.ZeroKnowledge.BooleanTestCost
import Zcash.Snark.ZeroKnowledge.ActionOracleStream

namespace Zcash.Snark.ZeroKnowledge
open MeasureTheory

/-- A Boolean instruction is measurable when its inputs and wires are, supplying the induction step
for probability-valued tests. -/
theorem BooleanTestInstruction.eval_measurable {Input Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
    (instruction : BooleanTestInstruction Input) (input : Ω → Input → Bool)
    (hinput : ∀ address, Measurable (fun sample => input sample address))
    (wires : Ω → List Bool) (hwires : Measurable wires) :
    Measurable (fun sample => instruction.eval (input sample) (wires sample)) := by
  cases instruction with
  | constant value => exact measurable_const
  | input address => exact hinput address
  | nand left right =>
    exact (Measurable.of_discrete : Measurable (fun values : List Bool =>
      !(values.getD left false && values.getD right false))).comp hwires

/-- Each finite circuit is measurable when its concrete input readers are measurable. -/
theorem runBooleanTest_measurable {Input Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
    (input : Ω → Input → Bool) (hinput : ∀ address, Measurable (fun sample => input sample address))
    (instructions : List (BooleanTestInstruction Input)) (wires : Ω → List Bool) (hwires : Measurable wires) :
    Measurable (fun sample => runBooleanTest (input sample) instructions (wires sample)) := by
  induction instructions generalizing wires with
  | nil => exact hwires
  | cons instruction later ih =>
    have hv := instruction.eval_measurable input hinput wires hwires
    have hn : Measurable (fun sample => instruction.eval (input sample) (wires sample) :: wires sample) :=
      (Measurable.of_discrete : Measurable (fun pair : Bool × List Bool => pair.1 :: pair.2)).comp (hv.prodMk hwires)
    exact ih _ hn

/-- A finite Boolean program defines a measurable event whenever its input reads do, allowing its
output probabilities to be compared. -/
theorem BooleanTestProgram.eval_measurable {Input Ω : Type*} [MeasurableSpace Ω]
    (program : BooleanTestProgram Input) (input : Ω → Input → Bool)
    (hinput : ∀ address, Measurable (fun sample => input sample address)) :
    Measurable (fun sample => program.eval (input sample)) := by
  letI : MeasurableSpace (List Bool) := ⊤
  letI : DiscreteMeasurableSpace (List Bool) := ⟨fun _ => trivial⟩
  have hw := runBooleanTest_measurable input hinput program.instructions (fun _ => []) measurable_const
  exact (Measurable.of_discrete : Measurable (fun wires : List Bool => wires.getD program.output false)).comp hw

end Zcash.Snark.ZeroKnowledge
