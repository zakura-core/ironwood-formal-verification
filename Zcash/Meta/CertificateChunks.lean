import Lean.Elab.Tactic

/-!
# Synchronous kernel checks for bounded source-certificate pieces

A piece is a function from its exact remaining certificate to its original
certificate. Each function is checked before the next piece is elaborated. The
caller composes the checked functions with the checked final value; no source
equation or semantic premise is removed by this representation.
-/

namespace Zcash.Meta
open Lean Meta Elab

register_option Zcash.sourceCertificate.chunkSteps : Nat := {
  defValue := 512
  descr := "maximum source-reduction steps between synchronous certificate checks"
}

/-- Close and kernel-check one exact source-certificate continuation. -/
def checkCertificateChunk (first last : MVarId) (compile : Bool) : MetaM Expr := do
  let firstType ← instantiateMVars (← first.getType)
  let lastType ← instantiateMVars (← last.getType)
  withLocalDeclD `remainingCertificate lastType fun remaining => do
    last.assign remaining
    let body ← instantiateMVars (mkMVar first)
    if body.hasMVar then throwError "unresolved certificate chunk values"
    let value ← mkLambdaFVars #[remaining] body
    let type ← mkForallFVars #[remaining] firstType
    let name ← mkAuxDeclName
    withOptions (Elab.async.set · false) do
      mkAuxDefinition name type value (compile := compile)

/-- Close and kernel-check the final piece, returning the checked declaration itself. -/
def checkCertificateValue (goal : MVarId) (compile : Bool) : MetaM Expr := do
  let target ← instantiateMVars (← goal.getType)
  let value ← instantiateMVars (mkMVar goal)
  if value.hasMVar then throwError "unresolved final certificate values"
  let name ← mkAuxDeclName
  withOptions (Elab.async.set · false) do
    mkAuxDefinition name target value (compile := compile)

end Zcash.Meta
