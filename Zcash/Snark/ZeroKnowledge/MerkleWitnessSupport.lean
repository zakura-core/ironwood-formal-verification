import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Sinsemilla.Merkle

/-!
# Read certificates for original Merkle piece witnesses

Each callback reads its named node cells and performs the specified bit slicing.
The level is a fixed argument. These equalities cover all field values, including
values that do not satisfy the eventual hash or canonicity constraints.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits
open Specs (bitrange)

/-- The level and low node bits use just the left node cell. -/
theorem merkle_waWit_support (level : ℕ) (node : AssignedCell Fp) :
    WitnessFunctionSupport [node] (fun env => ((Sinsemilla.Merkle.HashLayer.waWit level node).eval env)[0]) :=
  (witnessFunctionSupport_readCell node).map (fun value => ((level + 2 ^ 10 * bitrange value.val 0 240 : ℕ) : Fp))

/-- The first short subpiece uses the left node's high bits. -/
theorem merkle_wb1Wit_support (node : AssignedCell Fp) :
    WitnessFunctionSupport [node] (fun env => ((Sinsemilla.Merkle.HashLayer.wb1Wit node).eval env)[0]) :=
  (witnessFunctionSupport_readCell node).map (fun value => ((bitrange value.val 250 5 : ℕ) : Fp))

/-- The second short subpiece uses the right node's low bits. -/
theorem merkle_wb2Wit_support (node : AssignedCell Fp) :
    WitnessFunctionSupport [node] (fun env => ((Sinsemilla.Merkle.HashLayer.wb2Wit node).eval env)[0]) :=
  (witnessFunctionSupport_readCell node).map (fun value => ((bitrange value.val 0 5 : ℕ) : Fp))

/-- The cross-node piece uses both original node cells. -/
theorem merkle_wbWit_support (leftNode rightNode : AssignedCell Fp) :
    WitnessFunctionSupport [leftNode, rightNode]
      (fun env => ((Sinsemilla.Merkle.HashLayer.wbWit leftNode rightNode).eval env)[0]) :=
  ((witnessFunctionSupport_readCell leftNode).pair (witnessFunctionSupport_readCell rightNode)).map
    (fun values => ((bitrange values.1.val 240 10 + 2 ^ 10 * bitrange values.1.val 250 5 +
      2 ^ 15 * bitrange values.2.val 0 5 : ℕ) : Fp))

/-- The final piece uses the remaining right-node bits. -/
theorem merkle_wcWit_support (node : AssignedCell Fp) :
    WitnessFunctionSupport [node] (fun env => ((Sinsemilla.Merkle.HashLayer.wcWit node).eval env)[0]) :=
  (witnessFunctionSupport_readCell node).map (fun value => ((bitrange value.val 5 250 : ℕ) : Fp))

end Zcash.Snark.ZeroKnowledge
