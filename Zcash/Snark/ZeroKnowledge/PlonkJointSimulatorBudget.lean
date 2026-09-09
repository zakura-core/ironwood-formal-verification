import Zcash.Snark.ZeroKnowledge.PlonkVerifierHxCostBound
import Zcash.Snark.ZeroKnowledge.PublicOpeningCostBound
import Zcash.Snark.ZeroKnowledge.IpaPreparedInputCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkKeyCost
import Zcash.Snark.ZeroKnowledge.ChallengeReadCost

/-!
# Complete joint-simulator budget

The access envelope includes the actual stored mask and lookup-family lengths.
The full budget includes each preparation stage, the complete quotient, the
complete public opening, and the materialized IPA. Field and group prices are
explicit; key expression sizes are measured by the existing component budgets.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A common envelope for supplied input reads and every generated stored reader. -/
def plonkJointAccessBudget (actions baseRead read : ℕ) (key : StoredPlonkKey) : ℕ :=
  baseRead + 44 * actions + 2 * key.lookupInputs.length + 2 * key.lookupTables.length + read + 28

/-- The entire algebraic joint simulation has one explicit composite polynomial budget. -/
def plonkJointSimulatorCostBudget (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions baseRead wAccess : ℕ) (key : StoredPlonkKey)
    (ch : Challenges 11 (Fp × ℕ)) : ℕ :=
  let access := plonkJointAccessBudget actions baseRead read key
  let mask := (22 * actions + 10) * (baseRead + wAccess + ipaCosts.groupScale + 2) +
    (22 * actions + 10) * (22 * actions + 10) +
    (22 * actions) * (5 * baseRead + 32) + (22 * actions) * (22 * actions) + 2 * baseRead + 3
  let quotient := plonkVerifierHxCostBudget fieldCosts node equal read omegaAccess actions (22 * actions)
    access ch.x.2 ch.y.2 (key.gatesCosted read) (key.layoutCosted read)
    (key.lookupInputCosted read) (key.lookupTableCosted read) key.n key.blindingFactors key.chunkLen
  let opening := plonkPublicOpeningCostBudget fieldCosts ipaCosts.groupAdd ipaCosts.groupScale equal read omegaAccess
    actions (22 * actions) access access wAccess access access
    ch.x.2 ch.x1.2 ch.x2.2 ch.x4.2 ch.x3.2 1 1 1
  mask + ((22 * actions) * 3 + 1) + quotient +
    (opening + 5 * access + ipaSimulatorCostBudget ipaCosts 11 access + 11) + 3 * (read + 1) + 4

end Zcash.Snark.ZeroKnowledge
