import Zcash.Snark.ZeroKnowledge.ActivationCoverageData
import Zcash.Snark.ZeroKnowledge.GateIndexedCoverage
import Zcash.Snark.ZeroKnowledge.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.CoverageTreePiece
import Zcash.Meta.SourceReduction
import Zcash.Meta.CertificateChunks

/-!
# Bounded kernel certification of complete activation coverage

Source metadata and the comparison tree are normalized once, each with an exact
kernel-checked equality. Every configured gate or lookup master then receives a
separate checked predicate lemma. The final proof composes all those lemmas and
normalization equalities; no evaluated Boolean is admitted as a proof.
-/

namespace Zcash.Meta
open Lean Meta Elab Tactic
open Zcash.Snark.ZeroKnowledge

initialize registerTraceClass `Zcash.activationCoverage

private def checkedCoverageData (original : Expr) : MetaM (Expr × Expr) := do
  let (normalized, equality) ← SourceReduction.normalizeSourceData original
  if normalized.hasMVar then throwError "unresolved coverage data"
  let name ← mkAuxDeclName
  let stored ← withOptions (Elab.async.set · false) do
    -- Expand local let bindings while closing the value. The synchronous
    -- kernel checks the exact type and equality without a duplicate meta check
    -- of the growing tree's constructor proofs.
    mkAuxDefinition name (← inferType original) normalized
      (zetaDelta := true) (compile := false)
  let checked ← withOptions (Elab.async.set · false) do
    mkAuxTheorem (← mkEq original stored) equality (zetaDelta := true)
  resetCache
  return (stored, checked)

/-- Store one complete metadata list with a checked equality to its original source.
Separate declarations let each normalization use the default elaboration budget. -/
elab "certify_coverage_data" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOf ``SourceListCertificate do
    throwError "expected a SourceListCertificate goal"
  let source := target.getAppArgs.back!
  let (entries, equality) ← checkedCoverageData source
  goal.assign (← mkAppM ``SourceListCertificate.mk #[entries, ← mkEqSymm equality])
  replaceMainGoal []

/-- Check a bounded tree-construction prefix and retain its exact remaining fold. -/
elab "certify_coverage_tree_piece " limit:num : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``CoverageTreePiece do
      throwError "expected a CoverageTreePiece goal"
    let arguments := target.getAppArgs
    let comparison := arguments[arguments.size - 3]!
    let source := arguments[arguments.size - 2]!
    let initial := arguments.back!
    let elementType := (← inferType source).getAppArgs[0]!
    let mut entries := source
    let mut pieceEntries : Array Expr := #[]
    for _ in [:limit.getNat] do
      let reduced ← withTransparency .all (whnf entries)
      if reduced.isAppOf ``List.nil then
        entries := reduced
        break
      unless reduced.isAppOf ``List.cons do
        throwError "coverage labels do not reduce to a list"
      let arguments := reduced.getAppArgs
      pieceEntries := pieceEntries.push arguments[1]!
      entries := arguments[2]!
    let piece ← mkListLit elementType pieceEntries.toList
    let appended ← mkAppM ``List.append #[piece, entries]
    let hentries ← withOptions (Elab.async.set · false) do
      mkAuxTheorem (← mkEq source appended) (← mkEqRefl source)
    let initialData ← SourceReduction.reduceConstructorData initial
    let (tree, hstep) ← checkedCoverageData
      (← mkAppM ``coverageTreeFold #[comparison, piece, initialData])
    let finish ← withLocalDeclD `final (← inferType initial) fun final => do
      let remaining ← mkEq
        (mkAppN (mkConst ``coverageTreeFold) #[elementType, comparison, entries, tree]) final
      withLocalDeclD `remaining remaining fun hrest => do
        let proof := mkAppN (mkConst ``coverageTreeFold_chunk)
          #[elementType, comparison, source, piece, entries, initial, tree, final,
            hentries, hstep, hrest]
        mkLambdaFVars #[final, hrest] proof
    let record := mkAppN (mkConst ``CoverageTreePiece.mk)
      (arguments ++ #[entries, tree, finish])
    let stored ← withOptions (Elab.async.set · false) do
      mkAuxDefinition (← mkAuxDeclName) target record (zetaDelta := true) (compile := false)
    goal.assign stored
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln s!"[coverage tree piece] {← Term.getDeclName?}: checked {pieceEntries.size} entries; remainder empty: {entries.isAppOf ``List.nil}"
    replaceMainGoal []

private def coverageAllTarget (predicate entries : Expr) : MetaM Expr := do
  mkEq (← mkAppM ``coverageListAll #[predicate, entries]) (mkConst ``Bool.true)

private def checkedCoverageTree (gateScan : Bool) (originalEntries : Expr) : MetaM (Expr × Expr) := do
  let initial := mkConst (if gateScan then ``gateCoverageEmpty else ``lookupCoverageEmpty)
  let treeType ← inferType initial
  let comparison := treeType.getAppArgs[1]!
  let elementType := treeType.getAppArgs[0]!
  let final ← mkFreshExprMVar treeType
  let first ← mkFreshExprMVar (← mkEq
    (← mkAppM ``coverageTreeFold #[comparison, originalEntries, initial]) final)
  let mut goal := first.mvarId!
  let mut entries := originalEntries
  let mut tree := initial
  for count in [:10000] do
    let start := entries
    let mut pieceEntries : Array Expr := #[]
    for _ in [:32] do
      let reduced ← withTransparency .all (whnf entries)
      if reduced.isAppOf ``List.nil then break
      unless reduced.isAppOf ``List.cons do
        throwError "coverage labels do not reduce to a list"
      let arguments := reduced.getAppArgs
      pieceEntries := pieceEntries.push arguments[1]!
      entries := arguments[2]!
    if pieceEntries.isEmpty then
      final.mvarId!.assign tree
      goal.assign (← mkEqRefl tree)
      return (tree, ← checkCertificateValue first.mvarId! false)
    let piece ← mkListLit elementType pieceEntries.toList
    let appended ← mkAppM ``List.append #[piece, entries]
    let hentries ← withOptions (Elab.async.set · false) do
      mkAuxTheorem (← mkEq start appended) (← mkEqRefl start)
    let (next, hstep) ← checkedCoverageData (← mkAppM ``coverageTreeFold #[comparison, piece, tree])
    let nextGoal ← mkFreshExprMVar (← mkEq
      (← mkAppM ``coverageTreeFold #[comparison, entries, next]) final)
    goal.assign (← mkAppM ``coverageTreeFold_chunk
      #[comparison, start, piece, entries, tree, next, final, hentries, hstep, nextGoal])
    tree := next
    goal := nextGoal.mvarId!
    resetCache
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln s!"[activation coverage] kernel checked tree piece {count + 1}"
  throwError "coverage tree piece limit reached"

private def checkedCoverageAll (predicate originalEntries : Expr) : MetaM Expr := do
  let first ← mkFreshExprMVar (← coverageAllTarget predicate originalEntries)
  let mut goal := first.mvarId!
  let mut entries := originalEntries
  for count in [:10000] do
    let reduced ← withTransparency .all (whnf entries)
    if reduced.isAppOf ``List.nil then
      goal.assign (← mkEqRefl (mkConst ``Bool.true))
      return ← checkCertificateValue first.mvarId! false
    unless reduced.isAppOf ``List.cons do
      throwError "coverage entries do not reduce to a list at index {count}"
    let arguments := reduced.getAppArgs
    let entry := arguments[1]!
    let rest := arguments[2]!
    let target ← mkEq (mkApp predicate entry) (mkConst ``Bool.true)
    let value ← mkEqRefl (mkConst ``Bool.true)
    let checked ← withOptions (Elab.async.set · false) do
      mkAuxTheorem target value
    let next ← mkFreshExprMVar (← coverageAllTarget predicate rest)
    goal.assign (← mkAppM ``coverageListAll_cons #[predicate, entry, rest, checked, next])
    goal := next.mvarId!
    entries := rest
    resetCache
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln s!"[activation coverage] kernel checked configured entry {count + 1}"
  throwError "coverage entry limit reached"

/-- Check every configured predicate against separately certified metadata and tree data. -/
elab "check_coverage_predicates" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := target.eq? | throwError "expected a coverage conjunction equality"
  unless lhs.isAppOf ``coverageListAll && rhs.isConstOf ``Bool.true do
    throwError "expected coverageListAll ... = true"
  let arguments := lhs.getAppArgs
  goal.assign (← checkedCoverageAll arguments[arguments.size - 2]! arguments.back!)
  replaceMainGoal []

/-- Certify the full original tree scan through stored data and separately checked configured entries. -/
elab "check_activation_coverage" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := target.eq? | throwError "expected a coverage-scan equality"
    let gateScan := lhs.isAppOf ``gateActivationCoverageScan
    let indexedGateScan := lhs.isAppOf ``gateIndexedCoverageScan
    unless (gateScan || indexedGateScan || lhs.isAppOf ``lookupActivationCoverageScan) && rhs.isConstOf ``Bool.true do
      throwError "expected a gate, indexed gate, or lookup coverage scan equal to true"
    let arguments := lhs.getAppArgs
    let originalEntries := arguments[0]!
    let originalActivations := arguments[1]!
    let originalLabels := arguments[2]!
    let (entries, hentries) ← checkedCoverageData originalEntries
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln "[activation coverage] kernel checked normalized configured entries"
    let (activations, hactivations) ← checkedCoverageData originalActivations
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln "[activation coverage] kernel checked normalized activations"
    let (labels, hlabels) ← checkedCoverageData originalLabels
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln "[activation coverage] kernel checked all normalized input lists"
    let (tree, htree) ← checkedCoverageTree gateScan labels
    if ← isTracingEnabledFor `Zcash.activationCoverage then
      IO.eprintln "[activation coverage] kernel checked stored comparison tree"
    let predicateName := if gateScan then ``gateCoveragePredicate
      else if indexedGateScan then ``gateIndexedCoveragePredicate else ``lookupCoveragePredicate
    let predicate ← mkAppM predicateName #[activations, tree]
    let checked ← checkedCoverageAll predicate entries
    let theoremName := if gateScan then ``gateActivationCoverageScan_stored
      else if indexedGateScan then ``gateIndexedCoverageScan_stored else ``lookupActivationCoverageScan_stored
    let proof ← mkAppM theoremName #[originalEntries, entries, originalActivations, activations,
      originalLabels, labels, tree, hentries, hactivations, hlabels, htree, checked]
    goal.assign proof
    replaceMainGoal []

end Zcash.Meta
