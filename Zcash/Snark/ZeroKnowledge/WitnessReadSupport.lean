import Zcash.Snark.ZeroKnowledge.AdviceWitnessCausality

/-!
# Read support of structured witness expressions

The collectors retain every variable read, including both branches of a
conditional and every candidate in a dynamically indexed expression list. The
evaluation theorem therefore applies to all inputs and exceptional arithmetic
values. Native witness closures require their own dependency certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

mutual

/-- All cell atoms used by a field-sorted witness expression. -/
def fieldWitnessReads {F V : Type} : FExprOver F V → List V
  | .expr cell => [cell]
  | .envGet index => natWitnessReads index
  | .const _ | .localVar _ => []
  | .add left right | .mul left right => fieldWitnessReads left ++ fieldWitnessReads right
  | .inv value => fieldWitnessReads value
  | .ofNat value => natWitnessReads value
  | .ite condition yes no => boolWitnessReads condition ++ fieldWitnessReads yes ++ fieldWitnessReads no
  | .listGet values index => listWitnessReads values ++ natWitnessReads index
  | .dataGet _ _ row _ | .hintGet _ _ row _ => natWitnessReads row

/-- All cell atoms used by a dynamically indexed list of witness expressions. -/
def listWitnessReads {F V : Type} : List (FExprOver F V) → List V
  | [] => []
  | value :: rest => fieldWitnessReads value ++ listWitnessReads rest

/-- All cell atoms used by a Nat-sorted witness expression. -/
def natWitnessReads {F V : Type} : NExprOver F V → List V
  | .const _ | .idx | .localVar _ => []
  | .val value => fieldWitnessReads value
  | .add left right | .mul left right | .div left right | .mod left right
  | .land left right | .lor left right | .lxor left right
  | .shiftL left right | .shiftR left right => natWitnessReads left ++ natWitnessReads right
  | .ite condition yes no => boolWitnessReads condition ++ natWitnessReads yes ++ natWitnessReads no

/-- All cell atoms used by a witness condition. -/
def boolWitnessReads {F V : Type} : BExprOver F V → List V
  | .true | .false => []
  | .feq left right => fieldWitnessReads left ++ fieldWitnessReads right
  | .neq left right | .lt left right => natWitnessReads left ++ natWitnessReads right
  | .not value => boolWitnessReads value
  | .and left right => boolWitnessReads left ++ boolWitnessReads right

end

/-- Equal immutable context data and equal values for the declared variable reads. -/
structure WitnessContextAgreement {F Env V : Type} [WitgenEnv F Env V]
    (reads : List V) (left right : CtxOver F Env) : Prop where
  cellValues : ∀ cell ∈ reads, WitgenEnv.readVar (F := F) left.env cell = WitgenEnv.readVar right.env cell
  indexed : WitgenEnv.get (F := F) (V := V) left.env = WitgenEnv.get (V := V) right.env
  data : WitgenEnv.data (F := F) (V := V) left.env = WitgenEnv.data (V := V) right.env
  hints : WitgenEnv.hint (F := F) (V := V) left.env = WitgenEnv.hint (V := V) right.env
  locals : left.locals = right.locals
  index : left.idx = right.idx

/-- A context agreement also covers any subset of its declared reads. -/
theorem WitnessContextAgreement.mono {F Env V : Type} [WitgenEnv F Env V]
    {reads smaller : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (hsubset : smaller ⊆ reads) :
    WitnessContextAgreement smaller left right :=
  { agreement with cellValues := fun cell hcell => agreement.cellValues cell (hsubset hcell) }

/-- Context agreement for concatenated read lists restricts to the left fragment. -/
theorem WitnessContextAgreement.left {F Env V : Type} [WitgenEnv F Env V]
    {first second : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (first ++ second) left right) :
    WitnessContextAgreement first left right :=
  agreement.mono (List.subset_append_left _ _)

/-- Context agreement for concatenated read lists restricts to the right fragment. -/
theorem WitnessContextAgreement.right {F Env V : Type} [WitgenEnv F Env V]
    {first second : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (first ++ second) left right) :
    WitnessContextAgreement second left right :=
  agreement.mono (List.subset_append_right _ _)

variable {F Env V : Type} [FiniteField F] [WitgenEnv F Env V]

set_option maxHeartbeats 800000 in
mutual

/-- The field evaluator depends only on the collected reads and context data. -/
theorem fieldWitnessReads_eval (expression : FExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (fieldWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | expr cell => exact agreement.cellValues cell (List.mem_singleton_self _)
  | envGet index =>
    simp only [FExprOver.eval, agreement.indexed, natWitnessReads_eval index left right agreement]
  | const value => rfl
  | localVar index => simp only [FExprOver.eval, agreement.locals]
  | add a b =>
    simp only [FExprOver.eval, fieldWitnessReads_eval a left right agreement.left,
      fieldWitnessReads_eval b left right agreement.right]
  | mul a b =>
    simp only [FExprOver.eval, fieldWitnessReads_eval a left right agreement.left,
      fieldWitnessReads_eval b left right agreement.right]
  | inv value => simp only [FExprOver.eval, fieldWitnessReads_eval value left right agreement]
  | ofNat value => simp only [FExprOver.eval, natWitnessReads_eval value left right agreement]
  | ite condition yes no =>
    simp only [FExprOver.eval, boolWitnessReads_eval condition left right agreement.left.left,
      fieldWitnessReads_eval yes left right agreement.left.right,
      fieldWitnessReads_eval no left right agreement.right]
  | listGet values index =>
    simp only [FExprOver.eval, natWitnessReads_eval index left right agreement.right]
    exact listWitnessReads_eval values (index.eval right) left right agreement.left
  | dataGet key width row column =>
    simp only [FExprOver.eval, agreement.data, natWitnessReads_eval row left right agreement]
  | hintGet key width row column =>
    simp only [FExprOver.eval, agreement.hints, natWitnessReads_eval row left right agreement]

/-- Dynamic indexing introduces no undeclared read even when the index is out of bounds. -/
theorem listWitnessReads_eval (expressions : List (FExprOver F V)) (index : ℕ)
    (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (listWitnessReads expressions) left right) :
    FExprOver.evalList left index expressions = FExprOver.evalList right index expressions := by
  cases expressions with
  | nil => rfl
  | cons value rest =>
    cases index with
    | zero => exact fieldWitnessReads_eval value left right agreement.left
    | succ index => exact listWitnessReads_eval rest index left right agreement.right

/-- Nat arithmetic and bit operations depend only on the collected reads and context data. -/
theorem natWitnessReads_eval (expression : NExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (natWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | const value => rfl
  | val value => simp only [NExprOver.eval, fieldWitnessReads_eval value left right agreement]
  | idx => exact agreement.index
  | localVar index => simp only [NExprOver.eval, agreement.locals]
  | ite condition yes no =>
    simp only [NExprOver.eval, boolWitnessReads_eval condition left right agreement.left.left,
      natWitnessReads_eval yes left right agreement.left.right,
      natWitnessReads_eval no left right agreement.right]
  | add a b | mul a b | div a b | mod a b | land a b | lor a b | lxor a b | shiftL a b | shiftR a b =>
    simp only [NExprOver.eval, natWitnessReads_eval a left right agreement.left,
      natWitnessReads_eval b left right agreement.right]

/-- Branch conditions depend only on the collected reads and context data. -/
theorem boolWitnessReads_eval (expression : BExprOver F V) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (boolWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  cases expression with
  | true | false => rfl
  | feq a b =>
    simp only [BExprOver.eval, fieldWitnessReads_eval a left right agreement.left,
      fieldWitnessReads_eval b left right agreement.right]
  | neq a b | lt a b =>
    simp only [BExprOver.eval, natWitnessReads_eval a left right agreement.left,
      natWitnessReads_eval b left right agreement.right]
  | not value => simp only [BExprOver.eval, boolWitnessReads_eval value left right agreement]
  | and a b =>
    simp only [BExprOver.eval, boolWitnessReads_eval a left right agreement.left,
      boolWitnessReads_eval b left right agreement.right]

end

end Zcash.Snark.ZeroKnowledge
