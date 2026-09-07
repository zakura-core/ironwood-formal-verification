import Zcash.Snark.ZeroKnowledge.PlonkQueryLayout
import Zcash.Snark.ZeroKnowledge.GroupingDedup

/-!
# Disjoint Action blocks in the verifier query pattern

Only a single Action's finite layout needs kernel evaluation. Renaming its Action
index preserves its internal order, and the index distinguishes it from every
other Action and every shared commitment. These facts compose for arbitrary
bundle sizes.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Shift private commitment slots to later Actions; shared slots keep their identity. -/
def plonkShiftCommitmentId (offset : ℕ) : CommitmentId → CommitmentId
  | .instanceCol a c => .instanceCol (offset + a) c
  | .adviceCol a c => .adviceCol (offset + a) c
  | .permProduct a s => .permProduct (offset + a) s
  | .lookupProduct a l => .lookupProduct (offset + a) l
  | .lookupPermInput a l => .lookupPermInput (offset + a) l
  | .lookupPermTable a l => .lookupPermTable (offset + a) l
  | .fixedCol c => .fixedCol c
  | .permCommon c => .permCommon c
  | .vanishingH => .vanishingH
  | .randomPoly => .randomPoly

/-- Renaming an Action index never merges distinct commitment slots. -/
theorem plonkShiftCommitmentId_injective (offset : ℕ) :
    Function.Injective (plonkShiftCommitmentId offset) := by
  intro left right h
  cases left <;> cases right <;> simp_all [plonkShiftCommitmentId]

/-- The Action owning a private slot; shared commitments have no Action index. -/
def plonkCommitmentAction : CommitmentId → Option ℕ
  | .instanceCol a _ | .adviceCol a _ | .permProduct a _ | .lookupProduct a _
  | .lookupPermInput a _ | .lookupPermTable a _ => some a
  | .fixedCol _ | .permCommon _ | .vanishingH | .randomPoly => none

/-- One Action's commitments in first-appearance order. -/
def plonkPerActionCommitmentOrder (a : ℕ) : List CommitmentId :=
  [.instanceCol a 0] ++ List.ofFn (fun c : Fin 10 => .adviceCol a c.val) ++
    List.ofFn (fun s : Fin 3 => .permProduct a s.val) ++
    (List.ofFn (fun l : Fin 3 =>
      [.lookupProduct a l.val, .lookupPermInput a l.val, .lookupPermTable a l.val])).flatten

/-- Shared commitments, appended after all Action query blocks. -/
def plonkSharedCommitmentOrder : List CommitmentId :=
  List.ofFn (fun j : Fin 29 => .fixedCol (plonkFixedQueryOrder j).val) ++
    List.ofFn (fun j : Fin 15 => .permCommon j.val) ++ [.vanishingH, .randomPoly]

/-- Every shared commitment is opened only at the current-row point. -/
def plonkSharedQuerySpine : List (CommitmentId × Fin 4) :=
  plonkSharedCommitmentOrder.map fun id => (id, 0)

/-- First-appearance commitment order for the complete bundle. -/
def plonkCommitmentOrder (actions : ℕ) : List CommitmentId :=
  (List.finRange actions).flatMap (fun a => plonkPerActionCommitmentOrder a.val) ++
    plonkSharedCommitmentOrder

/-- The declared query stream consists of disjoint Action blocks and a shared suffix. -/
theorem plonkQuerySpine_eq_blocks (actions : ℕ) :
    plonkQuerySpine actions =
      (List.finRange actions).flatMap (fun a => plonkPerActionQuerySpine a.val) ++
        plonkSharedQuerySpine := by
  simp [plonkQuerySpine, plonkSharedQuerySpine, plonkSharedCommitmentOrder,
    List.ofFn_eq_map, List.flatMap_def, List.append_assoc]

/-- Every Action has the same local query pattern after renaming its index. -/
theorem plonkPerActionQuerySpine_shift (a : ℕ) :
    plonkPerActionQuerySpine a = (plonkPerActionQuerySpine 0).map
      (fun entry => (plonkShiftCommitmentId a entry.1, entry.2)) := by
  simp [plonkPerActionQuerySpine, plonkShiftCommitmentId]

/-- The same index renaming preserves local first-appearance commitment order. -/
theorem plonkPerActionCommitmentOrder_shift (a : ℕ) :
    plonkPerActionCommitmentOrder a =
      (plonkPerActionCommitmentOrder 0).map (plonkShiftCommitmentId a) := by
  simp [plonkPerActionCommitmentOrder, plonkShiftCommitmentId]

private theorem firstActionCommitmentOrder :
    dedupFold ((plonkPerActionQuerySpine 0).map Prod.fst) = plonkPerActionCommitmentOrder 0 := by
  decide +kernel

/-- The verifier discovers precisely the twenty-three local commitment slots in this order. -/
theorem plonkPerActionQuerySpine_commitments (a : ℕ) :
    dedupFold ((plonkPerActionQuerySpine a).map Prod.fst) = plonkPerActionCommitmentOrder a := by
  rw [plonkPerActionQuerySpine_shift, plonkPerActionCommitmentOrder_shift]
  have h := dedupFold_map (plonkShiftCommitmentId a)
    ((plonkPerActionQuerySpine 0).map Prod.fst)
    (fun _ _ _ _ h => plonkShiftCommitmentId_injective a h)
  simpa only [List.map_map, Function.comp_def, firstActionCommitmentOrder] using h

/-- All local commitment slots carry their block's Action index. -/
theorem plonkPerActionCommitmentOrder_action (a : ℕ) {id : CommitmentId}
    (hid : id ∈ plonkPerActionCommitmentOrder a) : plonkCommitmentAction id = some a := by
  simp only [plonkPerActionCommitmentOrder, List.mem_append, List.mem_singleton,
    List.mem_ofFn, List.mem_flatten] at hid
  rcases hid with ((rfl | ⟨c, rfl⟩) | ⟨s, rfl⟩) | ⟨entries, ⟨l, rfl⟩, hentry⟩
  · rfl
  · rfl
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl | rfl <;> rfl

/-- Every query in a local block belongs to that Action. -/
theorem plonkPerActionQuerySpine_action (a : ℕ) {entry : CommitmentId × Fin 4}
    (hentry : entry ∈ plonkPerActionQuerySpine a) : plonkCommitmentAction entry.1 = some a := by
  apply plonkPerActionCommitmentOrder_action a
  rw [← plonkPerActionQuerySpine_commitments, mem_dedupFold]
  exact List.mem_map.mpr ⟨entry, hentry, rfl⟩

/-- A shared commitment cannot be confused with any Action's private or instance slot. -/
theorem plonkSharedCommitmentOrder_action {id : CommitmentId}
    (hid : id ∈ plonkSharedCommitmentOrder) : plonkCommitmentAction id = none := by
  simp only [plonkSharedCommitmentOrder, List.mem_append, List.mem_ofFn,
    List.mem_cons, List.not_mem_nil, or_false] at hid
  rcases hid with (⟨j, rfl⟩ | ⟨j, rfl⟩) | rfl | rfl <;> rfl

/-- Distinct Actions have disjoint query commitment IDs, independently of point values. -/
theorem plonkPerActionQuerySpine_disjoint (a b : ℕ) (hab : a ≠ b) :
    List.Disjoint ((plonkPerActionQuerySpine a).map Prod.fst)
      ((plonkPerActionQuerySpine b).map Prod.fst) := by
  intro id ha hb
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp ha
  obtain ⟨other, hother, heq⟩ := List.mem_map.mp hb
  have ha := plonkPerActionQuerySpine_action a hentry
  have hb := plonkPerActionQuerySpine_action b hother
  rw [heq, ha] at hb
  exact hab (Option.some.inj hb)

/-- The shared commitment suffix contains no repeated slot. -/
theorem plonkSharedCommitmentOrder_nodup : plonkSharedCommitmentOrder.Nodup := by
  decide +kernel

/-- Deduplicating the entire query stream preserves the derived block-by-block commitment order. -/
theorem plonkQuerySpine_commitments (actions : ℕ) :
    dedupFold ((plonkQuerySpine actions).map Prod.fst) = plonkCommitmentOrder actions := by
  rw [plonkQuerySpine_eq_blocks]
  simp only [List.map_append, List.map_flatMap, plonkSharedQuerySpine, List.map_map,
    Function.comp_def]
  change dedupFold
    ((List.finRange actions).flatMap (fun a => (plonkPerActionQuerySpine a.val).map Prod.fst) ++
      plonkSharedCommitmentOrder.map id) = _
  rw [List.map_id]
  have hshared : List.Disjoint
      ((List.finRange actions).flatMap (fun a => (plonkPerActionQuerySpine a.val).map Prod.fst))
      plonkSharedCommitmentOrder := by
    intro id hid hshared
    obtain ⟨a, _, hid⟩ := List.mem_flatMap.mp hid
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hid
    have ha := plonkPerActionQuerySpine_action a.val hentry
    have hs := plonkSharedCommitmentOrder_action hshared
    rw [ha] at hs
    contradiction
  rw [groupingDedup_append_disjoint _ _ hshared,
    groupingDedup_flatMap _ _ (List.nodup_finRange actions)]
  · simp only [plonkPerActionQuerySpine_commitments]
    simp only [groupingDedup_reverse,
      List.dedup_eq_self.mpr (List.nodup_reverse.mpr plonkSharedCommitmentOrder_nodup),
      List.reverse_reverse, plonkCommitmentOrder]
  · intro a _ b _ hab
    exact plonkPerActionQuerySpine_disjoint a.val b.val (fun h => hab (Fin.ext h))

private theorem firstActionPoints :
    dedupFold ((plonkPerActionQuerySpine 0).map Prod.snd) = [0, 1, 2, 3] := by
  decide +kernel

/-- Every Action introduces the four rotation labels in the same first-appearance order. -/
theorem plonkPerActionQuerySpine_points (a : ℕ) :
    dedupFold ((plonkPerActionQuerySpine a).map Prod.snd) = [0, 1, 2, 3] := by
  rw [plonkPerActionQuerySpine_shift, List.map_map]
  exact firstActionPoints

/-- A nonempty bundle begins with Action zero's complete query block. -/
theorem plonkQuerySpine_head (actions : ℕ) :
    plonkQuerySpine (actions + 1) = plonkPerActionQuerySpine 0 ++
      ((List.ofFn (fun a : Fin actions => plonkPerActionQuerySpine (a.val + 1))).flatten ++
        plonkSharedQuerySpine) := by
  rw [plonkQuerySpine, List.ofFn_succ, List.flatten_cons]
  simp [plonkSharedQuerySpine, plonkSharedCommitmentOrder, List.append_assoc]

/-- After the first Action, no subsequent query can introduce another point label. -/
theorem plonkQuerySpine_points (actions : ℕ) (hpositive : 0 < actions) :
    dedupFold ((plonkQuerySpine actions).map Prod.snd) = [0, 1, 2, 3] := by
  cases actions with
  | zero => omega
  | succ actions =>
    rw [plonkQuerySpine_head, List.map_append]
    refine (groupingDedup_append_subset _ _ ?_).trans firstActionPoints
    intro point _
    apply mem_dedupFold.mp
    rw [firstActionPoints]
    fin_cases point <;> decide +kernel

/-- The actual pattern's point table is the four-label table for every positive Action count. -/
theorem plonkQueryPattern_points (actions k : ℕ) (hpositive : 0 < actions) :
    cisPts (plonkQueryPattern actions k) = [0, 1, 2, 3] := by
  rw [cisPts_eq_dedupFold, plonkQueryPattern, List.map_map]
  exact plonkQuerySpine_points actions hpositive

/-- A point label's table index is its natural-number value. -/
theorem plonkQueryPattern_pointIndex (actions k : ℕ) (hpositive : 0 < actions) (point : Fin 4) :
    cisPIdx (plonkQueryPattern actions k) point = point.val := by
  rw [cisPIdx, plonkQueryPattern_points actions k hpositive]
  fin_cases point <;> rfl

end Zcash.Snark.ZeroKnowledge
