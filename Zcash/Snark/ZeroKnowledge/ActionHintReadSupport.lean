import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Action.Circuit

/-!
# The fixed Action hint programs read no advice cells

These are the actual field, point, scalar, sibling, and swap programs supplied by
the Action source. Their values depend on immutable hints. The window result also
covers every original scalar-window builder, before any advice has been assigned.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen Zcash.Circuits
open Zcash.Circuits.Action

/-- The eight field builders in the original fixed Action private-input program. -/
def actionFieldHintPrograms : List (MOver Fp (AssignedCell Fp) (FExpr Fp)) :=
  [Circuit.hintWitnesses.psiOld, Circuit.hintWitnesses.rhoOld, Circuit.hintWitnesses.nk,
    Circuit.hintWitnesses.vOld, Circuit.hintWitnesses.vNew, Circuit.hintWitnesses.psiNew,
    Circuit.hintWitnesses.magnitude, Circuit.hintWitnesses.sign]

/-- The six point builders in that same original program. -/
def actionPointHintPrograms : List (MOver Fp (AssignedCell Fp) (Point (FExpr Fp))) :=
  [Circuit.hintWitnesses.cmOld, Circuit.hintWitnesses.gdOld, Circuit.hintWitnesses.akP,
    Circuit.hintWitnesses.pkDOld, Circuit.hintWitnesses.gdNew, Circuit.hintWitnesses.pkdNew]

/-- The five Nat-valued scalar builders passed to the original multiplication gadgets. -/
def actionScalarHintPrograms : List (MOver Fp (AssignedCell Fp) (NExpr Fp)) :=
  [Circuit.hintWitnesses.rcv, Circuit.hintWitnesses.alpha, Circuit.hintWitnesses.rivk,
    Circuit.hintWitnesses.rcmOld, Circuit.hintWitnesses.rcmNew]

/-- Every original field hint has an empty structured cell-read set. -/
theorem actionFieldHintPrograms_reads_nil (program : MOver Fp (AssignedCell Fp) (FExpr Fp))
    (hprogram : program ∈ actionFieldHintPrograms) : valueBuilderReads (value := field) program = [] := by
  simp only [actionFieldHintPrograms, List.mem_cons, List.not_mem_nil, or_false] at hprogram
  rcases hprogram with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every original point hint likewise reads no advice or fixed cell. -/
theorem actionPointHintPrograms_reads_nil (program : MOver Fp (AssignedCell Fp) (Point (FExpr Fp)))
    (hprogram : program ∈ actionPointHintPrograms) : valueBuilderReads (value := Point) program = [] := by
  simp only [actionPointHintPrograms, List.mem_cons, List.not_mem_nil, or_false] at hprogram
  rcases hprogram with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The five scalar programs read only immutable hints, so their cell-read sets are empty. -/
theorem actionScalarHintPrograms_reads_nil (program : MOver Fp (AssignedCell Fp) (NExpr Fp))
    (hprogram : program ∈ actionScalarHintPrograms) : natBuilderReads program = [] := by
  simp only [actionScalarHintPrograms, List.mem_cons, List.not_mem_nil, or_false] at hprogram
  rcases hprogram with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every original three-bit window builder inherits an empty cell-read set from its Action hint. -/
theorem actionScalarWindow_reads_nil (program : MOver Fp (AssignedCell Fp) (NExpr Fp))
    (hprogram : program ∈ actionScalarHintPrograms) (window : Fin 85) :
    valueBuilderReads (value := field) (Ecc.MulFixed.FullWidth.scalarWindows program)[window.val] = [] := by
  simp only [actionScalarHintPrograms, List.mem_cons, List.not_mem_nil, or_false] at hprogram
  rcases hprogram with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Ecc.MulFixed.FullWidth.scalarWindows, Vector.getElem_ofFn] <;> rfl

/-- The actual sibling callback depends only on the immutable hint store, at every layer index. -/
theorem actionMerkleSiblingHint_support (layer : ℕ) :
    WitnessFunctionSupport [] (fun env => ((Circuit.hintWitnesses.merkleSib layer).eval env)[0]) := by
  intro left right agreement
  have hh : left.env.hint = right.env.hint := agreement.hints
  change ((WitgenIROver.ofFExpr
      (.hintGet "orchard.action.merkle_sibling" 1 (.const layer) 0) : WitgenIR Fp 1).eval left)[0] =
    ((WitgenIROver.ofFExpr
      (.hintGet "orchard.action.merkle_sibling" 1 (.const layer) 0) : WitgenIR Fp 1).eval right)[0]
  rw [eval_ofFExpr_zero, eval_ofFExpr_zero]
  change ((left.env.hint "orchard.action.merkle_sibling" 1)[layer]?.getD default)[0] =
    ((right.env.hint "orchard.action.merkle_sibling" 1)[layer]?.getD default)[0]
  rw [hh]

/-- The actual native swap callback also depends only on that immutable store. -/
theorem actionMerkleSwapHint_support (layer : ℕ) :
    WitnessFunctionSupport [] (Circuit.hintWitnesses.merkleSwap layer) := by
  intro left right agreement
  have hh : left.env.hint = right.env.hint := agreement.hints
  change (((left.env.hint "orchard.action.merkle_swap" 1)[layer]?.getD default)[0] == 1) =
    (((right.env.hint "orchard.action.merkle_swap" 1)[layer]?.getD default)[0] == 1)
  rw [hh]

end Zcash.Snark.ZeroKnowledge
