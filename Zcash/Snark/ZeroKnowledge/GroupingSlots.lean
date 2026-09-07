import Zcash.Snark.Verifier.GroupingRef

/-!
# Slot-only description of the verifier's grouping

The routed ID lists depend on each commitment slot's first appearance and the
set of point indices queried for it. Projecting these data out of the existing
algorithm avoids reasoning about irrelevant commitment values and evaluations.
-/

namespace Zcash.Snark.ZeroKnowledge

section Slots

variable {k : ℕ} {F G : Type*}

private theorem slotFold (queries : List (VerifierQuery k F G))
    (acc : List (CommitmentId × CommitmentRef k F G)) :
    (queries.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
      else acc ++ [(q.commId, q.commitment)]) acc).map Prod.fst =
        (queries.map (·.commId)).foldl
          (fun ids id => if id ∈ ids then ids else ids ++ [id]) (acc.map Prod.fst) := by
  induction queries generalizing acc with
  | nil => rfl
  | cons q queries ih =>
    simp only [List.foldl_cons, List.map_cons]
    have htest : (acc.any (fun c => decide (c.1 = q.commId))) = true ↔
        q.commId ∈ acc.map Prod.fst := by
      simp only [List.any_eq_true, decide_eq_true_eq, List.mem_map]
    by_cases h : q.commId ∈ acc.map Prod.fst
    · rw [if_pos (htest.mpr h), if_pos h]
      exact ih acc
    · rw [if_neg (fun h' => h (htest.mp h')), if_neg h]
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        ih (acc ++ [(q.commId, q.commitment)])

/-- Projecting commitment IDs from the keyed fold gives ordinary first-appearance deduplication. -/
theorem groupingSlots_commitments (queries : List (VerifierQuery k F G)) :
    (cisComms queries).map Prod.fst = dedupFold (queries.map (·.commId)) :=
  slotFold queries []

variable [DecidableEq F]

/-- The ascending point-index set associated with a slot in the actual query list. -/
def groupingSlotIndices (queries : List (VerifierQuery k F G)) (id : CommitmentId) : List ℕ :=
  (List.range (cisPts queries).length).filter fun i =>
    ((queries.filter fun query => decide (query.commId = id)).map
      (fun query => cisPIdx queries query.point)).contains i

/-- The ordered slot and point-index pairs are independent of stored group values and evaluations. -/
theorem groupingSlots_data (queries : List (VerifierQuery k F G)) :
    (cisData queries).map (fun entry => (entry.1, entry.2.2.1)) =
      (dedupFold (queries.map (·.commId))).map (fun id => (id, groupingSlotIndices queries id)) := by
  rw [← groupingSlots_commitments, cisData, List.map_map, List.map_map]
  rfl

/-- The actual point-set table is first-appearance deduplication of the slot-index sets. -/
theorem groupingSlots_setList (queries : List (VerifierQuery k F G)) :
    cisSetList queries =
      dedupFold ((dedupFold (queries.map (·.commId))).map (groupingSlotIndices queries)) := by
  rw [cisSetList_eq_dedupFold]
  congr 1
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map Prod.snd) (groupingSlots_data queries)

/-- Actual routing filters the reversed slot order by its associated point-set index. -/
theorem groupingSlots_routed (queries : List (VerifierQuery k F G)) (i : ℕ) :
    (cisRouted queries i).map Prod.fst =
      (dedupFold (queries.map (·.commId))).reverse.filter (fun id =>
        decide ((cisSetList queries).findIdx
          (fun indices => decide (indices = groupingSlotIndices queries id)) = i)) := by
  have h := congrArg
    (fun entries : List (CommitmentId × List ℕ) =>
      (entries.reverse.filter fun entry => decide ((cisSetList queries).findIdx
        (fun indices => decide (indices = entry.2)) = i)).map Prod.fst)
    (groupingSlots_data queries)
  simp only [← List.map_reverse, List.filter_map, List.map_map, Function.comp_def] at h
  change (cisRouted queries i).map Prod.fst = List.map id _ at h
  simpa only [List.map_id] using h

/-- The verifier's complete ID grouping can be computed using only its slot order and point sets. -/
theorem groupingSlots_ids [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).ids =
      (List.range (cisSetList queries).length).map (fun i =>
        (dedupFold (queries.map (·.commId))).reverse.filter (fun id =>
          decide ((cisSetList queries).findIdx
            (fun indices => decide (indices = groupingSlotIndices queries id)) = i))) := by
  change (List.range (cisSetList queries).length).map (fun i => (cisRouted queries i).map Prod.fst) = _
  simp only [groupingSlots_routed]

end Slots

end Zcash.Snark.ZeroKnowledge
