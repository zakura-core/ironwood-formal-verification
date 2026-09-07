import Zcash.Snark.ZeroKnowledge.ActionInitialSelectorTrace
import Zcash.Snark.ZeroKnowledge.SelectorReplacementSupport

/-!
# Action's initial inactive selectors after compression

The source exclusion certificate and the compiler's root-assignment law show
that all nine previous-row selector replacements vanish at the initial row.
The valuation need only agree with the compiled value of the replacement's
single packed fixed query. No concrete selector-packing condition is supplied.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Every previous-row guard remains zero in the actual compiler's replacement
polynomial at row zero, even if another selector shares its packed column. -/
theorem actionCircuit_previousSelector_replacement_zero (selector : ℕ)
    (hselector : selector ∈ actionPreviousRowSelectors) {compressed : SelCompress}
    (hlookup : actionCircuit.selectorMap.lookup selector = some compressed)
    (valuation : Query → Fp)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (actionCircuit.fixedRows.getD compressed.packedCol []).getD 0 0) :
    (selReplacement compressed).eval valuation = 0 :=
  topLevelSelectorReplacement_zero_of_inactive actionCircuit
    (fun value => FiniteField.fromNat_F value) hlookup
    (actionCircuit_previousSelector_initial_inactive selector hselector) valuation hvalue

end Zcash.Snark.ZeroKnowledge
