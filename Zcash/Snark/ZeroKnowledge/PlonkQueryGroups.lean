import Zcash.Snark.ZeroKnowledge.PlonkQueryBlocks
import Zcash.Snark.ZeroKnowledge.GroupingSlots
import Zcash.Snark.ZeroKnowledge.PlonkCommitmentRouting

/-!
# The five opening groups derived from the verifier query layout

Each commitment slot has a fixed rotation set. Action indices distinguish the
slots but do not affect that set. The local finite classification therefore
determines the full bundle's grouping for every positive Action count.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The reference opening group determined by a commitment slot's kind and column. -/
def plonkCommitmentGroup : CommitmentId → Fin 5
  | .adviceCol _ c => if c ∈ [0, 2, 3, 4, 5] then 1 else 2
  | .permProduct _ s => if s = 2 then 1 else 3
  | .lookupProduct _ _ => 1
  | .lookupPermInput _ _ => 4
  | _ => 0

/-- The five ascending point-index sets, in first-appearance order. -/
def plonkGroupPointIndices : Fin 5 → List ℕ := ![[0], [0, 1], [0, 1, 2], [0, 1, 3], [0, 2]]

/-- The classifier uses the same point sets as the reference polynomial opening. -/
theorem plonkGroupPointIndices_eq_opening (i : Fin 5) :
    plonkGroupPointIndices i = (plonkOpeningPointIndices i).map Fin.val := by
  fin_cases i <;> rfl

/-- The point-index set assigned to one commitment slot. -/
def plonkCommitmentPointIndices (id : CommitmentId) : List ℕ :=
  plonkGroupPointIndices (plonkCommitmentGroup id)

/-- Renaming an Action index does not change its slot's opening group. -/
theorem plonkCommitmentGroup_shift (a : ℕ) (id : CommitmentId) :
    plonkCommitmentGroup (plonkShiftCommitmentId a id) = plonkCommitmentGroup id := by
  cases id <;> rfl

private theorem firstActionPointMembership :
    ∀ id ∈ plonkPerActionCommitmentOrder 0, ∀ point : Fin 4,
      (id, point) ∈ plonkPerActionQuerySpine 0 ↔ point.val ∈ plonkCommitmentPointIndices id := by
  decide +kernel

/-- The fixed local classification transfers to every Action's actual query block. -/
theorem plonkPerActionQuerySpine_pointMembership (a : ℕ) {id : CommitmentId}
    (hid : id ∈ plonkPerActionCommitmentOrder a) (point : Fin 4) :
    (id, point) ∈ plonkPerActionQuerySpine a ↔ point.val ∈ plonkCommitmentPointIndices id := by
  rw [plonkPerActionCommitmentOrder_shift] at hid
  obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hid
  rw [plonkPerActionQuerySpine_shift, plonkCommitmentPointIndices,
    plonkCommitmentGroup_shift, ← plonkCommitmentPointIndices,
    ← firstActionPointMembership base hbase point, List.mem_map]
  constructor
  · rintro ⟨entry, hentry, hpair⟩
    have hidEq := plonkShiftCommitmentId_injective a (congrArg Prod.fst hpair)
    have hpoint := congrArg Prod.snd hpair
    have hentryEq : entry = (base, point) := Prod.ext hidEq hpoint
    simpa only [hentryEq] using hentry
  · intro hentry
    exact ⟨(base, point), hentry, rfl⟩

/-- Local query membership is precisely slot membership together with its classified rotation. -/
theorem plonkPerActionQuerySpine_mem (a : ℕ) (id : CommitmentId) (point : Fin 4) :
    (id, point) ∈ plonkPerActionQuerySpine a ↔
      id ∈ plonkPerActionCommitmentOrder a ∧ point.val ∈ plonkCommitmentPointIndices id := by
  constructor
  · intro hquery
    have hid : id ∈ plonkPerActionCommitmentOrder a := by
      rw [← plonkPerActionQuerySpine_commitments, mem_dedupFold]
      exact List.mem_map.mpr ⟨(id, point), hquery, rfl⟩
    exact ⟨hid, (plonkPerActionQuerySpine_pointMembership a hid point).mp hquery⟩
  · rintro ⟨hid, hpoint⟩
    exact (plonkPerActionQuerySpine_pointMembership a hid point).mpr hpoint

/-- Every shared slot belongs to the singleton current-point group. -/
theorem plonkSharedCommitmentOrder_group {id : CommitmentId}
    (hid : id ∈ plonkSharedCommitmentOrder) : plonkCommitmentGroup id = 0 := by
  have h := plonkSharedCommitmentOrder_action hid
  cases id <;> simp_all [plonkCommitmentAction, plonkCommitmentGroup]

/-- The shared query suffix has the same slot-and-rotation membership characterization. -/
theorem plonkSharedQuerySpine_mem (id : CommitmentId) (point : Fin 4) :
    (id, point) ∈ plonkSharedQuerySpine ↔
      id ∈ plonkSharedCommitmentOrder ∧ point.val ∈ plonkCommitmentPointIndices id := by
  by_cases hid : id ∈ plonkSharedCommitmentOrder
  · have hgroup := plonkSharedCommitmentOrder_group hid
    fin_cases point <;>
      simp [plonkSharedQuerySpine, List.mem_map, Prod.mk.injEq, hid,
        plonkCommitmentPointIndices, hgroup, plonkGroupPointIndices]
  · simp [plonkSharedQuerySpine, List.mem_map, Prod.mk.injEq, hid]

/-- Composing the blocks preserves the slot's rotation set for arbitrary Action counts. -/
theorem plonkQuerySpine_mem (actions : ℕ) (id : CommitmentId) (point : Fin 4) :
    (id, point) ∈ plonkQuerySpine actions ↔
      id ∈ plonkCommitmentOrder actions ∧ point.val ∈ plonkCommitmentPointIndices id := by
  rw [plonkQuerySpine_eq_blocks]
  simp only [List.mem_append, List.mem_flatMap, plonkPerActionQuerySpine_mem,
    plonkSharedQuerySpine_mem, plonkCommitmentOrder]
  aesop

/-- The five classified sets are already sorted subsets of the four-label index range. -/
theorem plonkGroupPointIndices_filter (i : Fin 5) :
    (List.range 4).filter (fun j => decide (j ∈ plonkGroupPointIndices i)) =
      plonkGroupPointIndices i := by
  fin_cases i <;> rfl

/-- The pattern's commitment table has the structurally derived Action and shared order. -/
theorem plonkQueryPattern_commitments (actions k : ℕ) :
    dedupFold ((plonkQueryPattern actions k).map (·.commId)) = plonkCommitmentOrder actions := by
  rw [plonkQueryPattern, List.map_map]
  exact plonkQuerySpine_commitments actions

/-- The existing verifier computes exactly the classified point set for every present slot. -/
theorem plonkQueryPattern_slotIndices (actions k : ℕ) (hpositive : 0 < actions)
    {id : CommitmentId} (hid : id ∈ plonkCommitmentOrder actions) :
    groupingSlotIndices (plonkQueryPattern actions k) id = plonkCommitmentPointIndices id := by
  unfold groupingSlotIndices
  simp only [plonkQueryPattern_points actions k hpositive, List.length_cons, List.length_nil,
    plonkQueryPattern_pointIndex actions k hpositive]
  simp only [plonkQueryPattern, List.filter_map, List.map_map, Function.comp_def]
  change (List.range 4).filter (fun i =>
    (((plonkQuerySpine actions).filter (fun entry => decide (entry.1 = id))).map
      (fun entry => entry.2.val)).contains i) = plonkGroupPointIndices (plonkCommitmentGroup id)
  refine (List.filter_congr ?_).trans (plonkGroupPointIndices_filter _)
  intro i hi
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨entry, ⟨hentry, hidEq⟩, hindex⟩
    have hpoint := (plonkQuerySpine_mem actions entry.1 entry.2).mp hentry |>.2
    simpa only [hidEq, hindex] using hpoint
  · intro hpoint
    let point : Fin 4 := ⟨i, List.mem_range.mp hi⟩
    have hentry := (plonkQuerySpine_mem actions id point).mpr ⟨hid, hpoint⟩
    exact ⟨(id, point), ⟨hentry, rfl⟩, rfl⟩

private theorem firstActionGroups :
    dedupFold ((plonkPerActionCommitmentOrder 0).map plonkCommitmentPointIndices) =
      List.ofFn plonkGroupPointIndices := by
  decide +kernel

/-- The first Action's slots form the complete prefix of a nonempty bundle's commitment table. -/
theorem plonkCommitmentOrder_head (actions : ℕ) :
    plonkCommitmentOrder (actions + 1) = plonkPerActionCommitmentOrder 0 ++
      ((List.ofFn (fun a : Fin actions => plonkPerActionCommitmentOrder (a.val + 1))).flatten ++
        plonkSharedCommitmentOrder) := by
  rw [plonkCommitmentOrder, List.flatMap_def, ← List.ofFn_eq_map, List.ofFn_succ,
    List.flatten_cons, List.append_assoc]
  rfl

/-- The first Action introduces all five point sets, and later slots introduce none. -/
theorem plonkCommitmentOrder_pointSets (actions : ℕ) (hpositive : 0 < actions) :
    dedupFold ((plonkCommitmentOrder actions).map plonkCommitmentPointIndices) =
      List.ofFn plonkGroupPointIndices := by
  cases actions with
  | zero => omega
  | succ actions =>
    rw [plonkCommitmentOrder_head, List.map_append]
    refine (groupingDedup_append_subset _ _ ?_).trans firstActionGroups
    intro indices hindices
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp hindices
    apply mem_dedupFold.mp
    rw [firstActionGroups]
    exact List.mem_ofFn.mpr ⟨plonkCommitmentGroup id, rfl⟩

/-- The actual verifier discovers precisely the five reference point sets, in their declared order. -/
theorem plonkQueryPattern_setList (actions k : ℕ) (hpositive : 0 < actions) :
    cisSetList (plonkQueryPattern actions k) = List.ofFn plonkGroupPointIndices := by
  rw [groupingSlots_setList, plonkQueryPattern_commitments]
  have hmap : (plonkCommitmentOrder actions).map (groupingSlotIndices (plonkQueryPattern actions k)) =
      (plonkCommitmentOrder actions).map plonkCommitmentPointIndices := by
    apply List.map_congr_left
    intro id hid
    exact plonkQueryPattern_slotIndices actions k hpositive hid
  rw [hmap, plonkCommitmentOrder_pointSets actions hpositive]

/-- Looking up any classified point set returns its declared group index. -/
theorem plonkGroupPointIndices_findIdx (i : Fin 5) :
    (List.ofFn plonkGroupPointIndices).findIdx
      (fun indices => decide (indices = plonkGroupPointIndices i)) = i.val := by
  fin_cases i <;> rfl

/-- Filtering first-appearance slot order recovers each reference Horner list exactly. -/
theorem plonkCommitmentOrder_filter (actions : ℕ) (i : Fin 5) :
    (plonkCommitmentOrder actions).filter (fun id => decide (plonkCommitmentGroup id = i)) =
      plonkOpeningCommitmentIds actions i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [plonkCommitmentOrder, plonkOpeningCommitmentIds,
      plonkPerActionCommitmentOrder, plonkCommitmentGroup, plonkSharedCommitmentOrder,
      List.filter_flatMap, List.filter_append]
    rfl
  · simp only [plonkOpeningCommitmentIds, Fin.cons_succ]
    fin_cases j <;>
      simp [plonkCommitmentOrder, plonkPrivateGroupMembers,
        plonkPerActionCommitmentOrder, plonkCommitmentGroup, plonkSharedCommitmentOrder,
        plonkPrivateCommitmentId, List.filter_flatMap, List.map_flatMap, List.filter_append]

/-- Every actual pattern group has the reference commitment list in the verifier's reverse order. -/
theorem plonkQueryPattern_groupIds (actions k : ℕ) (hpositive : 0 < actions) (i : Fin 5) :
    (constructIntermediateSets (plonkQueryPattern actions k)).ids.getD i.val [] =
      (plonkOpeningCommitmentIds actions i).reverse := by
  rw [groupingSlots_ids, plonkQueryPattern_setList actions k hpositive,
    List.length_ofFn, plonkQueryPattern_commitments]
  rw [List.getD_eq_getElem _ _ (by
    simp only [List.length_map, List.length_range]
    exact i.isLt), List.getElem_map, List.getElem_range]
  rw [← plonkCommitmentOrder_filter actions i, ← List.filter_reverse]
  apply List.filter_congr
  intro id hid
  rw [plonkQueryPattern_slotIndices actions k hpositive (List.mem_reverse.mp hid)]
  simp only [plonkCommitmentPointIndices]
  simpa only [Fin.ext_iff] using
    congrArg (fun j : ℕ => decide (j = i.val))
      (plonkGroupPointIndices_findIdx (plonkCommitmentGroup id))

/-- The actual pattern's five node lists have exactly the reference ordering. -/
theorem plonkQueryPattern_groupNodes (actions k : ℕ) (hpositive : 0 < actions) :
    (constructIntermediateSets (plonkQueryPattern actions k)).points =
      [[0], [0, 1], [0, 1, 2], [0, 1, 3], [0, 2]] := by
  change (cisSetList (plonkQueryPattern actions k)).map (fun indices =>
    indices.filterMap (fun i => (cisPts (plonkQueryPattern actions k))[i]?)) = _
  rw [plonkQueryPattern_setList actions k hpositive, plonkQueryPattern_points actions k hpositive]
  rfl

end Zcash.Snark.ZeroKnowledge
