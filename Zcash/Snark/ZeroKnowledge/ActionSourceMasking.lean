import Zcash.Snark.ZeroKnowledge.ActionConfiguration
import Zcash.Snark.ZeroKnowledge.SourceExpressionMasking

/-!
# Masking certificates from the Action configure program

At the late boundaries, every selector is inactive. At row zero, only previous-row
advice can cross into the masked suffix. The source checks isolate the selectors
that must be zero to suppress those reads. These are structural certificates; the
compiler and placement still have to supply the stated selector valuations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action

/-- The Action gate selectors that suppress all previous-row advice dependencies. -/
def actionPreviousRowSelectors : List ℕ := [4, 10, 11, 13, 14, 15, 16, 21, 24]

/-- Configured selectors are zero after placement; at row zero only this subset is needed. -/
def actionSourceMaskZero (initial : Bool) : Query → Bool
  | .selector selector => selector.index < 56 && (!initial || selector.index ∈ actionPreviousRowSelectors)
  | _ => false

/-- Public queries are safe; current and next advice are additionally retained at row zero. -/
def actionSourceMaskSafe (initial : Bool) : Query → Bool
  | .advice _ rotation => initial && (rotation = 0 || rotation = 1)
  | _ => true

set_option maxRecDepth 10000 in
/-- All source Action gates pass both the initial and late boundary classifications. -/
theorem actionCircuit_sourceGateMaskCertificates :
    [true, false].all (fun initial => (flatGates actionCircuit.constraintSystem).all
      (sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial))) = true := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

set_option maxRecDepth 10000 in
/-- Every source lookup input passes both boundary classifications. -/
theorem actionCircuit_sourceLookupInputMaskCertificates :
    [true, false].all (fun initial => actionCircuit.constraintSystem.lookups.all fun argument =>
      argument.inputs.all
        (sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial))) = true := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

set_option maxRecDepth 10000 in
/-- Every source lookup-table expression passes both boundary classifications. -/
theorem actionCircuit_sourceLookupTableMaskCertificates :
    [true, false].all (fun initial => actionCircuit.constraintSystem.lookups.all fun argument =>
      argument.tables.all
        (sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial))) = true := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The source gate certificate applies to every configured polynomial and either boundary class. -/
theorem actionCircuit_sourceGateMaskSafe (initial : Bool) (expression : Expression Zcash.Arithmetic.Fp Query)
    (hexpression : expression ∈ flatGates actionCircuit.constraintSystem) :
    sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial) expression = true :=
  List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceGateMaskCertificates initial
    (by cases initial <;> simp)) expression hexpression

/-- The source input certificate applies to every member of every configured lookup. -/
theorem actionCircuit_sourceLookupInputMaskSafe (initial : Bool)
    (argument : LookupArgument Zcash.Arithmetic.Fp) (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (expression : Expression Zcash.Arithmetic.Fp Query) (hexpression : expression ∈ argument.inputs) :
    sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial) expression = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceLookupInputMaskCertificates
    initial (by cases initial <;> simp)) argument hargument) expression hexpression

/-- The source table certificate applies to every member of every configured lookup. -/
theorem actionCircuit_sourceLookupTableMaskSafe (initial : Bool)
    (argument : LookupArgument Zcash.Arithmetic.Fp) (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (expression : Expression Zcash.Arithmetic.Fp Query) (hexpression : expression ∈ argument.tables) :
    sourceExpressionMaskSafe (actionSourceMaskZero initial) (actionSourceMaskSafe initial) expression = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceLookupTableMaskCertificates
    initial (by cases initial <;> simp)) argument hargument) expression hexpression

end Zcash.Snark.ZeroKnowledge
