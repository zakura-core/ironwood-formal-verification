import Zcash.Snark.ZeroKnowledge.AdviceMapScan

/-!
# Original read checks factored through their placed addresses

Source equations can normalize the finite address data before any dependent
decidability proof is constructed. This factorization preserves the complete
original transition for every instruction and every map, including rejection.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- The original target and all original reads at the supplied placement. -/
def adviceReadAddressData {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (entry : SupportedAdviceProgram F) : AdviceAddress × List AdviceAddress :=
  (adviceProgramTarget entry.instruction, entry.reads.map (placedWitnessCell place))

/-- Apply the original availability policy to already placed address data. -/
def adviceReadAddressMapStep (roots : AdviceAliasMap)
    (data : AdviceAddress × List AdviceAddress) : Option AdviceAliasMap :=
  if data.2.all (fun address => decide (address.1.kind ≠ .advice ∨
      (adviceAliasMapLookup roots address).isSome = true)) then
    some (adviceAliasMapInsert roots data.1 data.1)
  else none

/-- Factoring out placement preserves every original map transition exactly. -/
theorem adviceReadMapStep_eq_addressStep {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (roots : AdviceAliasMap) (entry : SupportedAdviceProgram F) :
    adviceReadMapStep place roots entry = adviceReadAddressMapStep roots (adviceReadAddressData place entry) := by
  simp only [adviceReadMapStep, adviceReadAddressMapStep, adviceReadAddressData,
    List.all_map, Function.comp_def]
  rfl

end Zcash.Snark.ZeroKnowledge
