import Zcash.Circuits.Sinsemilla.Merkle

/-!
# From a defined canonical Merkle statement to the honest path computation

The application specification retains literal child encodings and guarded
Sinsemilla steps. Canonical encodings and defined hashes identify those messages
with the field-valued sibling/swap computation used by the witness generator.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Circuits.Sinsemilla.Merkle
open Zcash.Circuits.Sinsemilla.Merkle.CalculateRoot
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- Canonical field-valued sibling and Boolean swap readings for literal child encodings. -/
def canonicalMerkleReadings (left right : ℕ → ℕ) (side : ℕ → Bool) (index : ℕ) : Fp × Fp :=
  (if side index then (left index : Fp) else (right index : Fp), if side index then 1 else 0)

/-- A canonical encoded step feeds exactly the specified chunks to the honest hash computation. -/
theorem canonicalMerkleReadings_chunks (level left right : ℕ) (side : Bool) (node : Fp)
    (hleft : left < PALLAS_BASE_CARD) (hright : right < PALLAS_BASE_CARD)
    (hnode : (if side then (right : Fp) else (left : Fp)) = node) :
    proverChunks level node (if side then (left : Fp) else (right : Fp))
        ((if side then (1 : Fp) else 0) = 1) = merkleChunks level left right := by
  cases side with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hnode ⊢
    rw [← hnode]
    simp only [proverChunks, zero_ne_one, decide_false, Bool.false_eq_true, if_false, ZMod.val_natCast,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  | true =>
    simp only [if_true] at hnode ⊢
    rw [← hnode]
    simp only [proverChunks, decide_true, if_true, ZMod.val_natCast,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]

/-- Canonical, defined exact path data produces the specified root under the actual honest path fold. -/
theorem exactCanonicalMerklePath_pathNode (G : Generators) (Q : Point Fp)
    (level depth : ℕ) (start root : Fp) (left right : ℕ → ℕ) (side : ℕ → Bool)
    (hpath : ExactMerklePathData G Q level depth start root left right side)
    (hleft : ∀ index, index < depth → left index < PALLAS_BASE_CARD)
    (hright : ∀ index, index < depth → right index < PALLAS_BASE_CARD)
    (hdefined : ∀ index, index < depth →
      (hashToPoint G.S Q (merkleChunks (level + index) (left index) (right index))).isSome) :
    pathNode G Q level (canonicalMerkleReadings left right side) start depth = some root := by
  obtain ⟨nodes, hstart, hroot, hsteps⟩ := hpath
  have hprefix : ∀ count, count ≤ depth →
      pathNode G Q level (canonicalMerkleReadings left right side) start count = some (nodes count) := by
    intro count
    induction count with
    | zero => intro _; simpa only [pathNode] using congrArg some hstart.symm
    | succ count ih =>
      intro hcount
      have hi : count < depth := by omega
      rw [pathNode, ih (by omega), Option.bind_some]
      have hchunks := canonicalMerkleReadings_chunks (level + count) (left count) (right count)
        (side count) (nodes count) (hleft count hi) (hright count hi) (hsteps count hi).2.2.1
      change (hashToPoint G.S Q (proverChunks (level + count) (nodes count)
        (if side count then (left count : Fp) else (right count : Fp))
        ((if side count then (1 : Fp) else 0) = 1))).map (·.x) = _
      rw [hchunks]
      cases hh : hashToPoint G.S Q (merkleChunks (level + count) (left count) (right count)) with
      | none =>
        have hbad := hdefined count hi
        simp only [hh, Option.isSome_none, Bool.false_eq_true] at hbad
      | some point =>
        simpa only [Option.map_some] using congrArg some ((hsteps count hi).2.2.2 point hh).symm
  simpa only [hroot] using hprefix depth le_rfl

/-- Splitting the honest fold preserves both the prefix root and the exact suffix execution. -/
theorem pathNode_append (G : Generators) (Q : Point Fp) (level : ℕ)
    (path : ℕ → Fp × Fp) (start : Fp) (first rest : ℕ) :
    pathNode G Q level path start (first + rest) =
      (pathNode G Q level path start first).bind
        (fun middle => pathNode G Q (level + first) (fun i => path (first + i)) middle rest) := by
  induction rest with
  | zero =>
    simp only [Nat.add_zero, pathNode]
    cases pathNode G Q level path start first <;> rfl
  | succ rest ih =>
    rw [Nat.add_succ, pathNode, ih, Option.bind_assoc]
    apply congrArg (Option.bind (pathNode G Q level path start first))
    funext middle
    simp only [pathNode, Nat.add_assoc]

end Zcash.Snark.ZeroKnowledge
