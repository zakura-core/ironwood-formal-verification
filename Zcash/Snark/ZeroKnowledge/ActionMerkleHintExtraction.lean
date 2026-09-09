import Zcash.Snark.ZeroKnowledge.MerkleHintExtraction
import Zcash.Circuits.Action.Bundle

/-!
# The original Action's 32 auxiliary Merkle readings

The two original 16-layer calls retain exactly the supplied sibling programs and
Boolean swap flags, at source regions 8 through 263. This source-routing result
requires witness consistency and applies independently of hash definedness.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.constructorNameAsVariable false

/-- Both original Action Merkle halves retain exactly the supplied 32 path readings. -/
theorem actionMerkleHintCells_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (hints : Circuit.Witnesses Fp) (cfg : Circuit.Config)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Circuit.synthesizeBase generators bases hints cfg).operations self) self) :
    ∀ index, index < 32 →
      (Circuit.extract cfg hints self ⟨env.place, env.env.toEnvironment⟩).merklePath index =
        (((hints.merkleSib index).eval env)[0], if hints.merkleSwap index env then 1 else 0) := by
  simp only [Circuit.synthesizeBase, circuit_norm] at hw
  obtain ⟨_, hwChecks, _⟩ := hw
  simp only [Circuit.synthWitness_output, Circuit.synthWitness_nextRegionIndex,
    Circuit.synthWitness_regionCount, Nat.add_assoc,
    Circuit.synthChecks_eq, Circuit.synthChecksProgram, Circuit.loadPrivate,
    circuit_norm] at hwChecks
  obtain ⟨hwFirst, hwSecond, _, _, _, _, _, _, _⟩ := hwChecks
  have first := merkleFold_hintCells_of_extendsWitnesses generators bases.merkleQ
    bases.merkleQ_onCurve 0 16 (by norm_num) hints.merkleSib hints.merkleSwap
    (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) _ (self + 8) env hwFirst
  have second := merkleFold_hintCells_of_extendsWitnesses generators bases.merkleQ
    bases.merkleQ_onCurve 16 16 (by norm_num)
    (fun index => hints.merkleSib (16 + index))
    (fun index => hints.merkleSwap (16 + index))
    (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) _ (self + 136) env hwSecond
  intro index hindex
  by_cases hfirst : index < 16
  · obtain ⟨hsibling, hswap⟩ := first index hfirst
    simp only [Circuit.extract, if_pos hfirst]
    with_unfolding_all exact Prod.ext hsibling hswap
  · obtain ⟨hsibling, hswap⟩ := second (index - 16) (by omega)
    dsimp only at hsibling hswap
    simp only [show 16 + (index - 16) = index by omega] at hsibling hswap
    simp only [Circuit.extract, if_neg hfirst]
    with_unfolding_all exact Prod.ext hsibling hswap

end Zcash.Snark.ZeroKnowledge
