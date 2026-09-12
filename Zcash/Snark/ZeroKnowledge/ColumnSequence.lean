import Zcash.Snark.ZeroKnowledge.RowMaskSampling

/-!
# Successive masked columns with private dependencies

A column's retained rows may depend on the full contents of every earlier masked column.
Fresh suffix samples still hide the joint evaluation trace: the induction removes the
future columns for each fixed private history, then applies the current column's rank
theorem. Independence from just the previously disclosed evaluations is not assumed.

The constructors here are total functions. A prover that aborts while constructing a
column must separately connect its successful execution or charge that failure event.
All challenges and observation points are supplied parameters.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Earlier masked row vectors, most recently constructed first. -/
abbrev ColumnHistory (n : ℕ) := List (Fin n → Fp)

/-- A retained-row construction with its fixed suffix boundary. -/
structure ColumnStep (n : ℕ) where
  firstMasked : ℕ
  rows : ColumnHistory n → (Fin n → Fp)

/-- The number of selected row-mask samples, before counting any commitment blinds. -/
def columnRowSampleCount {n : ℕ} : List (ColumnStep n) → ℕ
  | [] => 0
  | step :: rest => (n - step.firstMasked) + columnRowSampleCount rest

/-- The tape budget is the sum of the declared suffix sizes. -/
theorem columnRowSampleCount_eq_sum {n : ℕ} (steps : List (ColumnStep n)) :
    columnRowSampleCount steps = (steps.map fun step => n - step.firstMasked).sum := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp [columnRowSampleCount, ih]

/-- Construct a column from its actual retained rows and increasing-row suffix tape. -/
def columnRowsFromCoins {n : ℕ} (step : ColumnStep n) (history : ColumnHistory n)
    (tape : Fin (n - step.firstMasked) → Fp) : Fin n → Fp :=
  maskedRows step.firstMasked (step.rows history) (rowMaskTapeEquiv n step.firstMasked tape)

/-- Compute every new column in emission order from a flat selected tape.

The private history passed to the next construction contains this entire masked column.
Commitment blinds are excluded from this selected row-mask subsequence. -/
def columnRowsFromTape {n : ℕ} : (steps : List (ColumnStep n)) → ColumnHistory n →
    (Fin (columnRowSampleCount steps) → Fp) → ColumnHistory n
  | [], _, _ => []
  | step :: rest, history, tape =>
    let coins := splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp tape
    let row := columnRowsFromCoins step history coins.1
    row :: columnRowsFromTape rest (row :: history) coins.2

/-- Exactly one new column is produced for each declared step. -/
theorem columnRowsFromTape_length {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount steps) → Fp) :
    (columnRowsFromTape steps history tape).length = steps.length := by
  induction steps generalizing history with
  | nil => rfl
  | cons step rest ih => simp [columnRowsFromTape, ih]

/-- Independent uniform suffix tapes, retaining the full private construction dependencies. -/
noncomputable def idealColumnRows {n : ℕ} : List (ColumnStep n) → ColumnHistory n → PMF (ColumnHistory n)
  | [], _ => PMF.pure []
  | step :: rest, history =>
    (PMF.uniformOfFintype (Fin (n - step.firstMasked) → Fp)).bind fun tape =>
      let row := columnRowsFromCoins step history tape
      (idealColumnRows rest (row :: history)).map (List.cons row)

/-- The ideal flat tape gives exactly the sequential private-row computation. -/
theorem uniformTapeColumnRows {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n) :
    (PMF.uniformOfFintype (Fin (columnRowSampleCount steps) → Fp)).map
        (columnRowsFromTape steps history) = idealColumnRows steps history := by
  induction steps generalizing history with
  | nil => exact PMF.map_const _ _
  | cons step rest ih =>
    change (PMF.uniformOfFintype (Fin ((n - step.firstMasked) + columnRowSampleCount rest) → Fp)).map
        ((fun coins : (Fin (n - step.firstMasked) → Fp) × (Fin (columnRowSampleCount rest) → Fp) =>
          let row := columnRowsFromCoins step history coins.1
          row :: columnRowsFromTape rest (row :: history) coins.2) ∘
            splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp) = _
    rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
      ← Zcash.independentProductPMF_uniform, Zcash.independentProductPMF, PMF.map_bind]
    unfold idealColumnRows
    congr 1
    funext tape
    simp only [PMF.map_comp, Function.comp_def]
    change (PMF.uniformOfFintype (Fin (columnRowSampleCount rest) → Fp)).map
      (List.cons (columnRowsFromCoins step history tape) ∘
        columnRowsFromTape rest (columnRowsFromCoins step history tape :: history)) = _
    rw [← PMF.map_comp, ih]

/-- Disclose every supplied evaluation of every newly constructed column, in emission order. -/
def observeColumnRows {n d : ℕ} (omega : Fp) (points : Fin d → Fp)
    (columns : ColumnHistory n) : List (Fin d → Fp) :=
  columns.map fun rows => fun i => (rowPolynomial omega rows).eval (points i)

/-- The explicit product law of independently uniform column evaluation vectors. -/
noncomputable def uniformColumnViews (d : ℕ) : ℕ → PMF (List (Fin d → Fp))
  | 0 => PMF.pure []
  | count + 1 => (PMF.uniformOfFintype (Fin d → Fp)).bind fun first =>
      (uniformColumnViews d count).map (List.cons first)

/-- Fresh suffix masks hide the entire evaluation trace despite private dependencies.

The retained-row constructor can read every previous masked row. The observation rank
conditions concern each fresh suffix, not the unknown earlier private history. -/
theorem idealColumnRows_joint_uniform {n d : ℕ} (steps : List (ColumnStep n))
    (history : ColumnHistory n) (omega : Fp) (points : Fin d → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ step ∈ steps, ∀ i : Fin d, ∀ j : Fin step.firstMasked, points i ≠ omega ^ j.val)
    (hsize : ∀ step ∈ steps, step.firstMasked + d ≤ n) :
    (idealColumnRows steps history).map (observeColumnRows omega points) =
      uniformColumnViews d steps.length := by
  induction steps generalizing history with
  | nil => simp [idealColumnRows, uniformColumnViews, observeColumnRows, PMF.map, PMF.pure_bind]
  | cons step rest ih =>
    have htail (history' : ColumnHistory n) :
        (idealColumnRows rest history').map (observeColumnRows omega points) =
          uniformColumnViews d rest.length :=
      ih history' (fun s hs => haway s (List.mem_cons_of_mem _ hs))
        (fun s hs => hsize s (List.mem_cons_of_mem _ hs))
    let disclose := rowEvaluationsFromTape step.firstMasked omega points (step.rows history)
    let finish := fun first : Fin d → Fp =>
      (uniformColumnViews d rest.length).map (List.cons first)
    have hstep (tape : Fin (n - step.firstMasked) → Fp) :
        ((idealColumnRows rest (columnRowsFromCoins step history tape :: history)).map
          (List.cons (columnRowsFromCoins step history tape))).map (observeColumnRows omega points) =
            finish (disclose tape) := by
      rw [PMF.map_comp]
      change (idealColumnRows rest (columnRowsFromCoins step history tape :: history)).map
        (List.cons (disclose tape) ∘ observeColumnRows omega points) = _
      rw [← PMF.map_comp, htail]
    rw [idealColumnRows, PMF.map_bind]
    simp_rw [hstep]
    change (PMF.uniformOfFintype (Fin (n - step.firstMasked) → Fp)).bind (finish ∘ disclose) = _
    rw [← PMF.bind_map]
    rw [uniformTapeRowEvaluations omega points (step.rows history) hrows hpoints
      (haway step List.mem_cons_self) (hsize step List.mem_cons_self)]
    rfl

/-- The selected row-mask tape under the wide-reduction law. -/
noncomputable def sampledColumnRows {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n) :
    PMF (ColumnHistory n) :=
  (sampleFieldsWith (columnRowSampleCount steps) (columnRowsFromTape steps history)).runFreshPMF fieldSample

/-- The whole sequential row computation costs one bias per selected suffix sample. -/
theorem sampledColumnRows_error_bound {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n) :
    PMFEventBiasLE (sampledColumnRows steps history) (idealColumnRows steps history)
        (columnRowSampleCount steps * challenge255Bias) ∧
      PMFEventBiasLE (idealColumnRows steps history) (sampledColumnRows steps history)
        (columnRowSampleCount steps * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (columnRowSampleCount steps) (columnRowsFromTape steps history)
  rw [uniformTapeColumnRows] at h
  exact h

end Zcash.Snark.ZeroKnowledge
