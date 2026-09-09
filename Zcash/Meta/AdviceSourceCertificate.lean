import Zcash.Meta.AdviceSupport
import Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate

/-!
# Source-preserving annotation certificates

This elaborator exposes the original operation list by definitional reduction
and the source's own opaque-value equations. It then attaches a semantic support
proof to each tagged instruction. Transport retains the exact annotation data.
The completed source certificate is checked synchronously by Lean's kernel.
Neither a successful alias scan nor a successful read scan is inferred here.
-/

namespace Zcash.Meta

open Lean Meta Elab Tactic
open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge

initialize registerTraceClass `Zcash.adviceSourceCertificate

private partial def isValueProjection (expression : Expr) : Bool :=
  match expression with
  | .lam _ _ body _ => isValueProjection body
  | .mdata _ body => isValueProjection body
  | _ => match expression.getAppFn with
    | .proj name 0 _ => name == ``Subtype
    | .const name _ => name == ``Subtype.val
    | _ => false

private def packedApplication? (environment : Lean.Environment) (e : Expr) :
    Option (Expr × Array Expr) := do
  let expanded := match e.getAppFn with
    | .const name levels =>
      match environment.find? name with
      | some (.defnInfo info) =>
        if isValueProjection info.value then
          (mkAppN (info.value.instantiateLevelParams info.levelParams levels) e.getAppArgs).headBeta
        else e
      | _ => e
    | _ => e
  let (packed, arguments) ← match expanded.getAppFn with
    | .proj name 0 packed =>
      if name != ``Subtype then none else some (packed, expanded.getAppArgs)
    | .const name _ =>
      let arguments := expanded.getAppArgs
      if name != ``Subtype.val || arguments.size < 3 then none
      else some (arguments[2]!, arguments.extract 3 arguments.size)
    | _ => none
  let some packedName := packed.getAppFn.constName? | none
  match environment.find? packedName with
  | some (.opaqueInfo _) => some (packed, arguments)
  | _ => none

private def certificateMotive (target selected : Expr) : MetaM Expr := do
  withLocalDeclD `source (← inferType selected) fun sourceVar => do
    let body := target.replace fun expression => if expression == selected then some sourceVar else none
    mkLambdaFVars #[sourceVar] body

private partial def findCertificateExprAux (environment : Lean.Environment)
    (expression : Expr) (predicate : Expr → Bool) : StateM (Std.HashSet Expr) (Option Expr) := do
  if (← get).contains expression then return none
  modify (·.insert expression)
  if predicate expression then return some expression
  match expression with
  | .app .. =>
    let arguments := expression.getAppArgs
    if let some name := expression.getAppFn.constName? then
      if let some (.recInfo info) := environment.find? name then
        if let some major := arguments[info.getMajorIdx]? then
          if let some found ← findCertificateExprAux environment major predicate then
            return some found
          let constructor := match major.getAppFn.constName? with
            | some name => match environment.find? name with
              | some (.ctorInfo _) => true
              | _ => false
            | none => major.isLit
          unless constructor do return none
    if expression.getAppFn.isProj then
      if let some found ← findCertificateExprAux environment expression.getAppFn predicate then
        return some found
    for argument in arguments.toList.reverse do
      if let some found ← findCertificateExprAux environment argument predicate then
        return some found
    findCertificateExprAux environment expression.getAppFn predicate
  | .proj _ _ body | .mdata _ body => findCertificateExprAux environment body predicate
  | .letE _ _ value _ _ => findCertificateExprAux environment value predicate
  | _ => return none

private def findCertificateExpr? (environment : Lean.Environment)
    (expression : Expr) (predicate : Expr → Bool) : Option Expr :=
  (findCertificateExprAux environment expression predicate).run' {}



private def nilFpCertificate : AdviceSourceCertificate ([] : List (PlacedAdviceProgram Fp × Option AdviceAddress)) :=
  AdviceSourceCertificate.nil

private def sourceCertificateProgress (message : String) : MetaM Unit := do
  if ← isTracingEnabledFor `Zcash.adviceSourceCertificate then
    IO.eprintln s!"[advice certificate] {message}"

private def transportCertificateSource (goal : MVarId) (source equality : Expr) : MetaM MVarId := do
  let target ← mkAppM ``AdviceSourceCertificate #[source]
  let next ← mkFreshExprMVar target
  let reverse ← mkEqSymm equality
  goal.assign (← mkAppM ``AdviceSourceCertificate.transport #[reverse, next])
  return next.mvarId!

-- Normalize finite constructor fields without traversing the arguments of an
-- opaque circuit call, which may contain the entire synthesis program.
private partial def reduceConstructorData (expression : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all (whnf expression)
  let some name := reduced.getAppFn.constName? | return reduced
  let some (.ctorInfo constructor) := (← getEnv).find? name | return reduced
  let mut arguments := reduced.getAppArgs
  for index in [constructor.numParams:arguments.size] do
    let argument := arguments[index]!
    unless ← isProof argument do
      arguments := arguments.set! index (← reduceConstructorData argument)
  return mkAppN reduced.getAppFn arguments

private def normalizeSourceData (original : Expr) : MetaM (Expr × Expr) := do
  let mut current := original
  let mut equality ← mkEqRefl original
  for _ in [:10000] do
    current ← reduceConstructorData current
    let environment ← getEnv
    let occurrence? := findCertificateExpr? environment current fun expression =>
      !expression.hasLooseBVars && (packedApplication? environment expression).isSome
    let some occurrence := occurrence? | return (current, equality)
    let some (packed, arguments) := packedApplication? environment occurrence | throwError "lost data equation"
    let mut proof ← mkAppM ``Subtype.property #[packed]
    for argument in arguments do
      if (← whnf (← inferType proof)).isForall then proof := mkApp proof argument
      else proof ← mkAppM ``congrFun #[proof, argument]
    let some (_, left, right) := (← whnf (← inferType proof)).eq? | throwError "expected a data equation"
    unless ← withTransparency .all (isDefEq left occurrence) do
      unless ← withTransparency .all (isDefEq right occurrence) do throwError "data equation does not match"
      proof ← mkEqSymm proof
    let some (_, _, replacement) := (← whnf (← inferType proof)).eq? | throwError "lost data replacement"
    let motive ← certificateMotive current occurrence
    equality ← mkEqTrans equality (← mkCongrArg motive proof)
    current := (mkApp motive replacement).headBeta
  throwError "finite source-data normalization limit reached"

/-- Annotate the original source, opening opaque source barriers only by their proved equations. -/
elab "certify_source_advice" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let originalTarget ← originalGoal.getType
    unless originalTarget.isAppOf ``AdviceSourceCertificate do
      throwError "expected an AdviceSourceCertificate goal"
    let mut goal := originalGoal
    let mut currentSource := originalTarget.getAppArgs.back!
    let mut count := 0
    for step in [:200000] do
      if step % 1000 == 0 then sourceCertificateProgress s!"step {step}: {count} annotated instructions"
      let reduced ← withTransparency .all (whnf currentSource)
      if reduced.isAppOf ``List.nil then
        goal.assign (mkConst ``nilFpCertificate)
        let value ← instantiateMVars (mkMVar originalGoal)
        if value.hasMVar then throwError "unresolved certificate values"
        let name ← mkAuxDeclName
        let _ ← withOptions (Elab.async.set · false) do
          mkAuxDefinition name originalTarget value (compile := false)
        sourceCertificateProgress s!"kernel checked {count} original instructions"
        replaceMainGoal []
        return
      if reduced.isAppOf ``List.cons then
        let arguments := reduced.getAppArgs
        let instruction := arguments[1]!
        let rest := arguments[2]!
        let (reads, support) ← annotateAdviceInstruction (← mkAppM ``Prod.fst #[instruction])
        let data ← mkAppM ``adviceSourceEntryData #[instruction, reads]
        let (normalized, equality) ← normalizeSourceData data
        let tailType ← mkAppM ``AdviceSourceCertificate #[rest]
        let tail ← mkFreshExprMVar tailType
        let value ← withTransparency .all <| mkAppM ``AdviceSourceCertificate.consWithData
          #[instruction, reads, support, normalized, ← mkEqSymm equality, tail]
        goal.assign value
        goal := tail.mvarId!
        currentSource := rest
        count := count + 1
        continue
      currentSource := reduced
      let environment ← getEnv
      let mut tried : Std.HashSet Expr := {}
      let mut occurrence? : Option Expr := none
      let mut advanced := false
      for _ in [:2000] do
        let some expression := findCertificateExpr? environment reduced (fun e =>
            !e.hasLooseBVars && !tried.contains e &&
              ((packedApplication? environment e).isSome ||
                e.isAppOf ``Circuit.operations || e.isAppOf ``RegionCircuit.operations ||
                e.isAppOf ``Circuit.output || e.isAppOf ``RegionCircuit.output ||
                e.isAppOf ``Circuit.nextRegionIndex || e.isProj ||
                e.isAppOf ``Prod.fst || e.isAppOf ``Prod.snd ||
                (match e.getAppFn with | .lam .. => true | _ => false) ||
                (match e with | .letE .. => true | _ => false)))
          | break
        tried := tried.insert expression
        if (packedApplication? environment expression).isSome then
          occurrence? := some expression
          break
        let replacement ← withTransparency .all (whnf expression)
        if replacement != expression then
          let motive ← certificateMotive reduced expression
          let newSource := (mkApp motive replacement).headBeta
          if newSource != reduced then
            currentSource := newSource
            advanced := true
            break
      if advanced then continue
      let some occurrence := occurrence? | throwError "source reduction stopped after {count} annotations: {reduced}"
      let some (packed, arguments) := packedApplication? environment occurrence | throwError "lost equation"
      let mut proof ← mkAppM ``Subtype.property #[packed]
      for argument in arguments do
        if (← whnf (← inferType proof)).isForall then proof := mkApp proof argument
        else proof ← mkAppM ``congrFun #[proof, argument]
      let some (_, left, right) := (← whnf (← inferType proof)).eq? | throwError "expected a source equation"
      unless ← withTransparency .all (isDefEq left occurrence) do
        unless ← withTransparency .all (isDefEq right occurrence) do throwError "source equation does not match"
        proof ← mkAppM ``Eq.symm #[proof]
      let some (_, _, replacement) := (← whnf (← inferType proof)).eq? | throwError "lost equality"
      let motive ← certificateMotive reduced occurrence
      let newSource := (mkApp motive replacement).headBeta
      goal ← transportCertificateSource goal newSource (← mkCongrArg motive proof)
      currentSource := newSource
    throwError "source certificate step limit reached"


end Zcash.Meta
