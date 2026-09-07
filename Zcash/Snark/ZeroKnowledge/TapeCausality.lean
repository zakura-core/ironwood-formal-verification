import Zcash.Snark.ZeroKnowledge.BatchedTape

/-!
# The randomness decoder ignores retained-row computations

Two column schedules with the same suffix boundaries split corresponding tape
positions into the same masks and blinds, even when their retained-row functions
differ. The statements compare positions directly so that equal lengths need no
choice of transport proof. No probability law or witness-validity premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Equal values at corresponding positions, allowing different dependent length expressions. -/
def TapeAgrees {F : Type*} {m n : ℕ} (left : Fin m → F) (right : Fin n → F) : Prop :=
  ∀ i j, i.val = j.val → left i = right j

/-- On a common index type, agreement at positions is equality of the complete tapes. -/
theorem TapeAgrees.eq {F : Type*} {n : ℕ} {left right : Fin n → F}
    (h : TapeAgrees left right) : left = right := funext fun i => h i i rfl

private theorem split_agrees {F : Type*} {m n m' n' : ℕ}
    (left : Fin (m + n) → F) (right : Fin (m' + n') → F)
    (hm : m = m') (h : TapeAgrees left right) :
    TapeAgrees (splitTapeEquiv m n F left).1 (splitTapeEquiv m' n' F right).1 ∧
      TapeAgrees (splitTapeEquiv m n F left).2 (splitTapeEquiv m' n' F right).2 := by
  subst m'
  constructor
  · intro i j hij
    exact h _ _ hij
  · intro i j hij
    exact h _ _ (congrArg (m + ·) hij)

private theorem join_left {F : Type*} {m n : ℕ}
    (first : Fin m → F) (rest : Fin n → F) (i : Fin m) :
    (splitTapeEquiv m n F).symm (first, rest) (Fin.castAdd n i) = first i :=
  congrArg (fun parts => parts.1 i) ((splitTapeEquiv m n F).apply_symm_apply (first, rest))

private theorem join_right {F : Type*} {m n : ℕ}
    (first : Fin m → F) (rest : Fin n → F) (i : Fin n) :
    (splitTapeEquiv m n F).symm (first, rest) (Fin.natAdd m i) = rest i :=
  congrArg (fun parts => parts.2 i) ((splitTapeEquiv m n F).apply_symm_apply (first, rest))

private theorem join_agrees {F : Type*} {m n m' n' : ℕ}
    (first : Fin m → F) (rest : Fin n → F)
    (first' : Fin m' → F) (rest' : Fin n' → F)
    (hm : m = m') (hfirst : TapeAgrees first first') (hrest : TapeAgrees rest rest') :
    TapeAgrees ((splitTapeEquiv m n F).symm (first, rest))
      ((splitTapeEquiv m' n' F).symm (first', rest')) := by
  subst m'
  intro i j hij
  by_cases hi : i.val < m
  · let a : Fin m := ⟨i.val, hi⟩
    let b : Fin m := ⟨j.val, by omega⟩
    have ha : i = Fin.castAdd n a := Fin.ext rfl
    have hb : j = Fin.castAdd n' b := Fin.ext rfl
    rw [ha, hb, join_left, join_left]
    exact hfirst a b hij
  · let a : Fin n := ⟨i.val - m, by omega⟩
    let b : Fin n' := ⟨j.val - m, by omega⟩
    have ha : i = Fin.natAdd m a := Fin.ext (by dsimp [a]; omega)
    have hb : j = Fin.natAdd m b := Fin.ext (by dsimp [b]; omega)
    rw [ha, hb, join_right, join_right]
    exact hrest a b (by dsimp [a, b]; omega)

private theorem cons_agrees {F : Type*} {n n' : ℕ} (first first' : F)
    (rest : Fin n → F) (rest' : Fin n' → F)
    (hfirst : first = first') (hrest : TapeAgrees rest rest') :
    TapeAgrees (Fin.cons first rest) (Fin.cons first' rest') := by
  intro i j hij
  by_cases hi : i.val = 0
  · have ha : i = 0 := Fin.ext hi
    have hb : j = 0 := Fin.ext (by simpa only [Fin.val_zero] using hij.symm.trans hi)
    simpa only [ha, hb, Fin.cons_zero] using hfirst
  · let a : Fin n := ⟨i.val - 1, by omega⟩
    let b : Fin n' := ⟨j.val - 1, by omega⟩
    have ha : i = a.succ := Fin.ext (by dsimp [a]; omega)
    have hb : j = b.succ := Fin.ext (by dsimp [b]; omega)
    rw [ha, hb, Fin.cons_succ, Fin.cons_succ]
    exact hrest a b (by dsimp [a, b]; omega)

/-- The full and row-only budgets, and the number of blinds, use only suffix boundaries. -/
theorem columnTapeCounts_shape {n : ℕ} (left right : List (ColumnStep n))
    (hshape : left.map ColumnStep.firstMasked = right.map ColumnStep.firstMasked) :
    columnRowSampleCount left = columnRowSampleCount right ∧
      left.length = right.length ∧ columnFullSampleCount left = columnFullSampleCount right := by
  have hrow : columnRowSampleCount left = columnRowSampleCount right := by
    simp only [columnRowSampleCount_eq_sum]
    have h := congrArg (List.map (fun first => n - first)) hshape
    simpa only [List.map_map, Function.comp_def] using congrArg List.sum h
  have hlen : left.length = right.length := by
    simpa only [List.length_map] using congrArg List.length hshape
  exact ⟨hrow, hlen, by rw [columnFullSampleCount_eq, columnFullSampleCount_eq, hrow, hlen]⟩

/-- The canonical decoder selects the same row masks and blinds regardless of retained-row functions. -/
theorem columnCoinEquiv_shape_congr {n : ℕ} (left right : List (ColumnStep n))
    (hshape : left.map ColumnStep.firstMasked = right.map ColumnStep.firstMasked)
    (tape : Fin (columnFullSampleCount left) → Fp)
    (tape' : Fin (columnFullSampleCount right) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees (columnCoinEquiv left tape).1 (columnCoinEquiv right tape').1 ∧
      TapeAgrees (columnCoinEquiv left tape).2 (columnCoinEquiv right tape').2 := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | cons step rest => simp at hshape
  | cons step rest ih =>
    cases right with
    | nil => simp at hshape
    | cons step' rest' =>
      obtain ⟨hfirst, hrest⟩ := List.cons.inj (by simpa only [List.map_cons] using hshape)
      have hsplit := split_agrees tape tape' (congrArg (n - ·) hfirst) htape
      have hnext := split_agrees _ _ rfl hsplit.2
      have hlater := ih rest' hrest _ _ hnext.2
      simp only [columnCoinEquiv_cons_apply]
      exact ⟨join_agrees _ _ _ _ (congrArg (n - ·) hfirst) hsplit.1 hlater.1,
        cons_agrees _ _ _ _ (hnext.1 0 0 rfl) hlater.2⟩

private theorem columnCoinEquiv_cons_symm_apply {n : ℕ}
    (step : ColumnStep n) (rest : List (ColumnStep n))
    (rows : Fin (columnRowSampleCount (step :: rest)) → Fp)
    (blinds : Fin (step :: rest).length → Fp) :
    (columnCoinEquiv (step :: rest)).symm (rows, blinds) =
      let first := splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp rows
      let blind := firstTapeEquiv rest.length blinds
      (splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp).symm
        (first.1, (splitTapeEquiv 1 (columnFullSampleCount rest) Fp).symm
          (blind.1, (columnCoinEquiv rest).symm (first.2, blind.2))) := rfl

/-- Recombining masks and blinds likewise depends only on suffix boundaries. -/
theorem columnCoinEquiv_symm_shape_congr {n : ℕ} (left right : List (ColumnStep n))
    (hshape : left.map ColumnStep.firstMasked = right.map ColumnStep.firstMasked)
    (rows : Fin (columnRowSampleCount left) → Fp)
    (rows' : Fin (columnRowSampleCount right) → Fp)
    (blinds : Fin left.length → Fp) (blinds' : Fin right.length → Fp)
    (hrows : TapeAgrees rows rows') (hblinds : TapeAgrees blinds blinds') :
    TapeAgrees ((columnCoinEquiv left).symm (rows, blinds))
      ((columnCoinEquiv right).symm (rows', blinds')) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact fun i => Fin.elim0 i
    | cons step rest => simp at hshape
  | cons step rest ih =>
    cases right with
    | nil => simp at hshape
    | cons step' rest' =>
      obtain ⟨hfirst, hrest⟩ := List.cons.inj (by simpa only [List.map_cons] using hshape)
      have hsplit := split_agrees rows rows' (congrArg (n - ·) hfirst) hrows
      have hhead : TapeAgrees (firstTapeEquiv rest.length blinds).1
          (firstTapeEquiv rest'.length blinds').1 := fun _ _ _ => hblinds 0 0 rfl
      have htail : TapeAgrees (firstTapeEquiv rest.length blinds).2
          (firstTapeEquiv rest'.length blinds').2 := by
        intro i j hij
        exact hblinds i.succ j.succ (congrArg (· + 1) hij)
      have hlater := ih rest' hrest _ _ _ _ hsplit.2 htail
      simp only [columnCoinEquiv_cons_symm_apply]
      exact join_agrees _ _ _ _ (congrArg (n - ·) hfirst) hsplit.1
        (join_agrees _ _ _ _ rfl hhead hlater)

private theorem casts_agree {F : Type*} {m n m' n' : ℕ}
    (hsize : m = n) (hsize' : m' = n')
    (left : Fin m → F) (right : Fin m' → F) (h : TapeAgrees left right) :
    TapeAgrees (Equiv.cast (congrArg (fun count => Fin count → F) hsize) left)
      (Equiv.cast (congrArg (fun count => Fin count → F) hsize') right) := by
  subst n
  subst n'
  exact h

/-- The batched sample budget and flattened shape depend only on the boundaries in each batch. -/
theorem batchedTapeCounts_shape {n : ℕ} (left right : List (List (ColumnStep n)))
    (hshape : left.map (List.map ColumnStep.firstMasked) = right.map (List.map ColumnStep.firstMasked)) :
    batchedColumnSampleCount left = batchedColumnSampleCount right ∧
      left.flatten.map ColumnStep.firstMasked = right.flatten.map ColumnStep.firstMasked := by
  have hflat : left.flatten.map ColumnStep.firstMasked = right.flatten.map ColumnStep.firstMasked := by
    simpa only [List.map_flatten] using congrArg List.flatten hshape
  refine ⟨?_, hflat⟩
  rw [batchedColumnSampleCount_eq, batchedColumnSampleCount_eq]
  exact (columnTapeCounts_shape _ _ hflat).2.2

/-- Converting all source batches preserves corresponding tape positions across constructor changes. -/
theorem batchedToColumnTape_shape_congr {n : ℕ} (left right : List (List (ColumnStep n)))
    (hshape : left.map (List.map ColumnStep.firstMasked) = right.map (List.map ColumnStep.firstMasked))
    (tape : Fin (batchedColumnSampleCount left) → Fp)
    (tape' : Fin (batchedColumnSampleCount right) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees (batchedToColumnTape left tape) (batchedToColumnTape right tape') := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact fun i => Fin.elim0 i
    | cons block rest => simp at hshape
  | cons block rest ih =>
    cases right with
    | nil => simp at hshape
    | cons block' rest' =>
      obtain ⟨hblock, hrest⟩ := List.cons.inj (by simpa only [List.map_cons] using hshape)
      have hcounts := columnTapeCounts_shape block block' hblock
      have hsplit := split_agrees tape tape' (congrArg₂ (· + ·) hcounts.1 hcounts.2.1) htape
      have hcoins := split_agrees _ _ hcounts.1 hsplit.1
      have hfirst := columnCoinEquiv_symm_shape_congr block block' hblock _ _ _ _ hcoins.1 hcoins.2
      have hlater := ih rest' hrest _ _ hsplit.2
      change TapeAgrees (Equiv.cast _ _) (Equiv.cast _ _)
      apply casts_agree (columnFullSampleCount_append block rest.flatten).symm
        (columnFullSampleCount_append block' rest'.flatten).symm
      exact join_agrees _ _ _ _ hcounts.2.2 hfirst hlater

/-- Batch conversion preserves the shared twelve-sample suffix without consulting constructors. -/
theorem batchedPreIpaTapeEquiv_shape_congr {n : ℕ} (left right : List (List (ColumnStep n)))
    (hshape : left.map (List.map ColumnStep.firstMasked) = right.map (List.map ColumnStep.firstMasked))
    (tape : Fin (batchedColumnSampleCount left + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount right + 12) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees (batchedPreIpaTapeEquiv left tape) (batchedPreIpaTapeEquiv right tape') := by
  have hcounts := batchedTapeCounts_shape left right hshape
  have hsplit := split_agrees tape tape' hcounts.1 htape
  have hcolumns := batchedToColumnTape_shape_congr left right hshape _ _ hsplit.1
  exact join_agrees _ _ _ _ (columnTapeCounts_shape _ _ hcounts.2).2.2 hcolumns hsplit.2

/-- The entire canonical pre-IPA decoder ignores retained-row functions. -/
theorem preIpaCoinEquiv_shape_congr {n : ℕ} (left right : List (ColumnStep n))
    (hshape : left.map ColumnStep.firstMasked = right.map ColumnStep.firstMasked)
    (tape : Fin (preIpaSampleCount left) → Fp)
    (tape' : Fin (preIpaSampleCount right) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees (preIpaCoinEquiv left tape).1 (preIpaCoinEquiv right tape').1 ∧
      (preIpaCoinEquiv left tape).2.1 = (preIpaCoinEquiv right tape').2.1 ∧
      TapeAgrees (preIpaCoinEquiv left tape).2.2 (preIpaCoinEquiv right tape').2.2 := by
  have hcounts := columnTapeCounts_shape left right hshape
  have hsplit := split_agrees tape tape' hcounts.2.2 htape
  have hcolumns := columnCoinEquiv_shape_congr left right hshape _ _ hsplit.1
  have hextra := split_agrees (m := 2) (n := 10) (m' := 2) (n' := 10) _ _ rfl hsplit.2
  refine ⟨hcolumns.1, ?_, ?_⟩
  · exact Prod.ext (hextra.1 0 0 rfl) (hextra.1 1 1 rfl)
  · exact join_agrees _ _ _ _ hcounts.2.1 hcolumns.2 hextra.2

/-- The complete batched decoder has the same masks, linear coefficients, and blinds at every position. -/
theorem batchedPreIpaCoins_shape_congr {n : ℕ} (left right : List (List (ColumnStep n)))
    (hshape : left.map (List.map ColumnStep.firstMasked) = right.map (List.map ColumnStep.firstMasked))
    (tape : Fin (batchedColumnSampleCount left + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount right + 12) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees (preIpaCoinEquiv left.flatten (batchedPreIpaTapeEquiv left tape)).1
        (preIpaCoinEquiv right.flatten (batchedPreIpaTapeEquiv right tape')).1 ∧
      (preIpaCoinEquiv left.flatten (batchedPreIpaTapeEquiv left tape)).2.1 =
        (preIpaCoinEquiv right.flatten (batchedPreIpaTapeEquiv right tape')).2.1 ∧
      TapeAgrees (preIpaCoinEquiv left.flatten (batchedPreIpaTapeEquiv left tape)).2.2
        (preIpaCoinEquiv right.flatten (batchedPreIpaTapeEquiv right tape')).2.2 :=
  preIpaCoinEquiv_shape_congr _ _ (batchedTapeCounts_shape left right hshape).2 _ _
    (batchedPreIpaTapeEquiv_shape_congr left right hshape tape tape' htape)

end Zcash.Snark.ZeroKnowledge
