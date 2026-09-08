import Zcash.Snark.ZeroKnowledge.ActionNativeCopies
import Zcash.Snark.ZeroKnowledge.AdviceAliasCollection

/-!
# Source-level certificates for shared base-coordinate writes

Column separation excludes accumulator and slope callbacks from the native copy
annotations. The remaining writes are the two original base-coordinate callbacks,
whose exact evaluator equations supply the copy semantics.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits.Ecc

/-- Every annotation names one base column at its immediately preceding local row. -/
def PreviousBaseCopySources (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (baseX baseY : Column .advice) : Prop :=
  ∀ column row address, source region column row = some address →
    (column = baseX ∨ column = baseY) ∧
      address = (column.toAny, ((place region + (row - 1) : ℕ) : ℤ))

/-- The accumulator, slopes, and running sum occupy different columns from the base. -/
def MulIncompleteBaseSeparated (cfg : MulIncomplete.Config) : Prop :=
  ∀ column ∈ [cfg.z, cfg.xA, cfg.lambda1, cfg.lambda2],
    column ≠ cfg.xP ∧ column ≠ cfg.yP

/-- A non-base write cannot receive a base-copy annotation. -/
theorem previousBaseCopySources_nonbase (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : MulIncomplete.Config)
    (hsource : PreviousBaseCopySources place source region cfg.xP cfg.yP)
    (hseparated : MulIncompleteBaseSeparated cfg)
    (column : Column .advice) (hcolumn : column ∈ [cfg.z, cfg.xA, cfg.lambda1, cfg.lambda2])
    (row : ℕ) (address : AdviceAddress) : source region column row ≠ some address := by
  intro heq
  rcases (hsource column row address heq).1 with hx | hy
  · exact (hseparated column hcolumn).1 hx
  · exact (hseparated column hcolumn).2 hy

/-- Every tagged native program in the original incomplete round is the certified base copy. -/
theorem mulIncomplete_round_nativeCopiesSound (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : MulIncomplete.Config) (offset bit : ℕ)
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (hsource : PreviousBaseCopySources place source region cfg.xP cfg.yP)
    (hseparated : MulIncompleteBaseSeparated cfg) :
    RegionNativeCopiesSound place source region
      (((MulIncomplete.round bit).call cfg offset alpha).operations region) := by
  intro column row callback hmem address haddress
  rw [FormalRegionCircuit.call_operations] at hmem
  simp only [MulIncomplete.round, circuit_norm] at hmem
  rcases hmem with hgate | hz | hxA | hl1 | hl2 | hxP | hyP
  · cases hgate
  · cases hz
    exact False.elim (previousBaseCopySources_nonbase place source region cfg hsource hseparated cfg.z (by simp) _ _ haddress)
  · cases hxA
    exact False.elim (previousBaseCopySources_nonbase place source region cfg hsource hseparated cfg.xA (by simp) _ _ haddress)
  · cases hl1
    exact False.elim (previousBaseCopySources_nonbase place source region cfg hsource hseparated cfg.lambda1 (by simp) _ _ haddress)
  · cases hl2
    exact False.elim (previousBaseCopySources_nonbase place source region cfg hsource hseparated cfg.lambda2 (by simp) _ _ haddress)
  · cases hxP
    rw [(hsource _ _ _ haddress).2]
    simpa only [placedWitnessCell, MulIncomplete.reads, AssignedCell.of_cell, Nat.add_sub_cancel]
      using mulIncomplete_baseX_copySemantics place cfg.xP (place region + (offset + 2))
        alpha (MulIncomplete.reads cfg offset region) bit
  · cases hyP
    rw [(hsource _ _ _ haddress).2]
    simpa only [placedWitnessCell, MulIncomplete.reads, AssignedCell.of_cell, Nat.add_sub_cancel]
      using mulIncomplete_baseY_copySemantics place cfg.yP (place region + (offset + 2))
        alpha (MulIncomplete.reads cfg offset region) bit

end Zcash.Snark.ZeroKnowledge
