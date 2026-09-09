import Zcash.Circuits.Sinsemilla.Merkle

/-!
# Exact path readings from the original Merkle witness programs

The conditional swap writes its supplied sibling and Boolean flag exactly.
The source-preserving layer and fold bridges propagate those readings to every
layer below the actual fold depth, without hash-definedness or gate-validity
premises. The loop placement is proved from the original eight-region layer.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits
open Zcash.Circuits.Sinsemilla.Merkle
open Zcash.Circuits.Sinsemilla.Merkle.CalculateRoot
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] CondSwap.swap Layer.circuit circuit

/-- The original conditional-swap region retains its sibling and Boolean hint. -/
theorem condSwap_hintCells_of_extendsWitnesses
    (cfg : CondSwap.Config) (sibling : WitgenIR Fp 1)
    (swap : Placed ProverEnvironment Fp → Bool) (input : Var CondSwap.Input Fp)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      (((CondSwap.swap sibling swap).call cfg 0 input).operations self)) :
    env.env.advice cfg.b ↑(env.place self) = (sibling.eval env)[0] ∧
    env.env.advice cfg.swap ↑(env.place self) = (if swap env then 1 else 0) := by
  rw [FormalRegionCircuit.call_operations] at hw
  simp only [CondSwap.swap, circuit_norm] at hw
  exact ⟨hw.2.1, hw.2.2.1⟩

/-- One original Merkle layer retains the supplied path readings. -/
theorem merkleLayer_hintCells_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (point : Point Fp) (hon : point.OnCurve)
    (level : ℕ) (hlevel : level < 2^10)
    (sibling : WitgenIR Fp 1) (swap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((Layer.circuit generators point hon level hlevel sibling swap).call cfg input).operations self) self) :
    env.env.advice cfg.1.b ↑(env.place self) = (sibling.eval env)[0] ∧
    env.env.advice cfg.1.swap ↑(env.place self) = (if swap env then 1 else 0) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Layer.circuit, circuit_norm] at hw
  exact condSwap_hintCells_of_extendsWitnesses cfg.1 sibling swap _ self env hw.1

/-- The original Merkle fold enters layer i at source region self + 8i. -/
theorem merkleHintFold_region
    (generators : Specs.Sinsemilla.Generators) (point : Point Fp) (hon : point.OnCurve)
    (level : ℕ) (siblings : ℕ → WitgenIR Fp 1)
    (swaps : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (self : ℕ) : ∀ index : ℕ,
    (FormalCircuit.foldState (layerAt generators point hon level siblings swaps)
      toInput cfg input self index).2 = self + 8 * index
  | 0 => rfl
  | index + 1 => by
    with_unfolding_all
      change (FormalCircuit.foldState (layerAt generators point hon level siblings swaps)
        toInput cfg input self index).2 + 8 = self + 8 * (index + 1)
    rw [merkleHintFold_region generators point hon level siblings swaps cfg input self index,
      Nat.mul_succ, Nat.add_assoc]

/-- Every retained path reading below the original fold depth equals its supplied hint. -/
theorem merkleFold_hintCells_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (point : Point Fp) (hon : point.OnCurve)
    (level depth : ℕ) (hdepth : level + depth ≤ 2^10)
    (siblings : ℕ → WitgenIR Fp 1) (swaps : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((circuit generators point hon level depth hdepth siblings swaps).call cfg input).operations self) self) :
    ∀ index, index < depth →
    env.env.advice cfg.1.b ↑(env.place (self + 8*index)) = ((siblings index).eval env)[0] ∧
    env.env.advice cfg.1.swap ↑(env.place (self + 8*index)) = (if swaps index env then 1 else 0) := by
  rw [FormalCircuit.call_operations] at hw
  with_unfolding_all
    change ExtendsWitnesses env.place env.env
      (((FormalCircuit.foldCall (layerAt generators point hon level siblings swaps)
        toInput cfg input depth >>= fun result => pure result.node) : Circuit Fp (Var field Fp)).operations self) self at hw
  simp only [Circuit.operations_bind, Circuit.operations_pure, List.append_nil,
    FormalCircuit.foldCall_operations, FormalCircuit.foldOps_extendsWitnesses] at hw
  intro index hindex
  have hi := hw ⟨index, hindex⟩
  rw [merkleHintFold_region generators point hon level siblings swaps cfg input self index] at hi
  exact merkleLayer_hintCells_of_extendsWitnesses generators point hon _ _ _ _ _ _ _ env hi

end Zcash.Snark.ZeroKnowledge
