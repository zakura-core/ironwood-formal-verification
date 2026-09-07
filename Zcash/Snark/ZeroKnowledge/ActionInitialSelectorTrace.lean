import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.ActionSourceMasking
import Zcash.Snark.ZeroKnowledge.SelectorInitialTrace

/-!
# Initial inactivity of Action's previous-row selectors

The concrete source trace excludes the nine selectors that guard previous-row
advice reads at every local row zero. Nonnegative placement preserves this fact.
This concerns original selectors; the packed fixed-column values remain separate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits.Action

/-- The complete Action source trace passes the initial exclusion check. -/
theorem actionSourceSelectorTrace_initialCheck :
    initialSelectorCheck actionPreviousRowSelectors (actionSourceSelectorTrace actionConfig) = true := by
  decide +kernel

/-- No previous-row selector is enabled at global row zero in the actual compiler. -/
theorem actionCircuit_previousSelector_initial_inactive (selector : ℕ)
    (hselector : selector ∈ actionPreviousRowSelectors) :
    (selector, 0) ∉ actionCircuit.selectorActivations := by
  rw [actionCircuit_selectorActivations_eq_sourceTrace]
  exact initialSelectorCheck_not_mem_placed actionPreviousRowSelectors
    (actionSourceSelectorTrace actionConfig) actionSourceSelectorTrace_initialCheck
    actionCircuit.regionStarts 0 selector hselector

end Zcash.Snark.ZeroKnowledge
