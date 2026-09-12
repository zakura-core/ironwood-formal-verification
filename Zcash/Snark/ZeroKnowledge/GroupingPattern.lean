import Zcash.Snark.Verifier.GroupingRef

/-!
# Transporting a finite query pattern to verifier challenges

A finite pattern records the ordered commitment IDs and abstract point labels.
Injectively interpreting those labels as field elements preserves the actual
verifier's grouping, including its member order and duplicate-query check. No
condition on commitment values or claimed evaluations is needed.
-/

namespace Zcash.Snark.ZeroKnowledge

section Pattern

variable {k : ℕ} {P F A G : Type*}
  [DecidableEq P] [DecidableEq F] [Zero P] [Zero F] [Inhabited A] [Inhabited G]

omit [Zero P] [Zero F] [Inhabited A] [Inhabited G] in
/-- The distinct-point table commutes with an injective interpretation of a query pattern. -/
theorem groupingPattern_points (pattern : List (VerifierQuery k P A))
    (queries : List (VerifierQuery k F G)) (interpret : P → F)
    (hinjective : Function.Injective interpret)
    (hpoints : queries.map (·.point) = pattern.map (fun q => interpret q.point)) :
    cisPts queries = (cisPts pattern).map interpret := by
  rw [cisPts_eq_dedupFold, cisPts_eq_dedupFold (qs := pattern), hpoints]
  simpa only [List.map_map, Function.comp_def] using
    dedupFold_map interpret (pattern.map (·.point)) (fun _ _ _ _ h => hinjective h)

/-- Matching ID and interpreted-point streams give exactly the same reference query list. -/
theorem groupingPattern_reference (pattern : List (VerifierQuery k P A))
    (queries : List (VerifierQuery k F G)) (interpret : P → F)
    (hinjective : Function.Injective interpret)
    (hids : queries.map (·.commId) = pattern.map (·.commId))
    (hpoints : queries.map (·.point) = pattern.map (fun q => interpret q.point)) :
    refQueries queries = refQueries pattern := by
  have hlength : queries.length = pattern.length := by
    simpa only [List.length_map] using congrArg List.length hids
  have htable := groupingPattern_points pattern queries interpret hinjective hpoints
  apply List.ext_getElem (by simp only [refQueries_length, hlength])
  intro n hn hn'
  have hq : n < queries.length := by simpa only [refQueries_length] using hn
  have hp : n < pattern.length := by simpa only [refQueries_length] using hn'
  have hid : queries[n].commId = pattern[n].commId := by
    have h := congrArg (fun l : List CommitmentId => l[n]?) hids
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hq,
      List.getElem?_eq_getElem hp, Option.map_some, Option.some.injEq] using h
  have hpoint : queries[n].point = interpret pattern[n].point := by
    have h := congrArg (fun l : List F => l[n]?) hpoints
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hq,
      List.getElem?_eq_getElem hp, Option.map_some, Option.some.injEq] using h
  have hindex : cisPIdx queries queries[n].point = cisPIdx pattern pattern[n].point := by
    rw [cisPIdx, htable, hpoint]
    exact findIdx_map_inj interpret (cisPts pattern)
      (point_mem_cisPts (List.getElem_mem hp)) (fun _ _ h => hinjective h)
  rw [refQueries_getElem queries hn, refQueries_getElem pattern hn',
    List.getD_eq_getElem _ _ hq, List.getD_eq_getElem _ _ hp, hindex, hid]

variable [DecidableEq A] [DecidableEq G]

/-- The actual verifier routes exactly the pattern's ordered commitment-ID lists. -/
theorem groupingPattern_ids (pattern : List (VerifierQuery k P A))
    (queries : List (VerifierQuery k F G)) (interpret : P → F)
    (hinjective : Function.Injective interpret)
    (hids : queries.map (·.commId) = pattern.map (·.commId))
    (hpoints : queries.map (·.point) = pattern.map (fun q => interpret q.point)) :
    (constructIntermediateSets queries).ids = (constructIntermediateSets pattern).ids := by
  rw [constructIntermediateSets_ref_ids queries,
    groupingPattern_reference pattern queries interpret hinjective hids hpoints,
    ← constructIntermediateSets_ref_ids pattern]

/-- The actual verifier's ordered node lists are the interpreted pattern node lists. -/
theorem groupingPattern_nodes (pattern : List (VerifierQuery k P A))
    (queries : List (VerifierQuery k F G)) (interpret : P → F)
    (hinjective : Function.Injective interpret)
    (hids : queries.map (·.commId) = pattern.map (·.commId))
    (hpoints : queries.map (·.point) = pattern.map (fun q => interpret q.point)) :
    (constructIntermediateSets queries).points =
      (constructIntermediateSets pattern).points.map (List.map interpret) := by
  have htable := groupingPattern_points pattern queries interpret hinjective hpoints
  have href := groupingPattern_reference pattern queries interpret hinjective hids hpoints
  have hsets : cisSetList queries = cisSetList pattern := by
    rw [← cisSetList_ref queries, href, cisSetList_ref pattern]
  change (cisSetList queries).map (fun s => s.filterMap (fun i => (cisPts queries)[i]?)) =
    ((cisSetList pattern).map (fun s => s.filterMap (fun i => (cisPts pattern)[i]?))).map _
  rw [hsets, htable, List.map_map]
  simp only [Function.comp_def, List.map_filterMap, List.getElem?_map]

omit [DecidableEq A] [DecidableEq G] in
/-- Duplicate commitment-point rejection is determined by the same finite pattern. -/
theorem groupingPattern_duplicates (pattern : List (VerifierQuery k P A))
    (queries : List (VerifierQuery k F G)) (interpret : P → F)
    (hinjective : Function.Injective interpret)
    (hids : queries.map (·.commId) = pattern.map (·.commId))
    (hpoints : queries.map (·.point) = pattern.map (fun q => interpret q.point)) :
    hasDuplicateCommitmentPoint queries = hasDuplicateCommitmentPoint pattern := by
  rw [hasDuplicateCommitmentPoint_ref queries,
    groupingPattern_reference pattern queries interpret hinjective hids hpoints,
    ← hasDuplicateCommitmentPoint_ref pattern]

end Pattern

end Zcash.Snark.ZeroKnowledge
