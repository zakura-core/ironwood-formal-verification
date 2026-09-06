import Zcash.Snark.ZeroKnowledge.ColumnSequence

/-!
# Interleaved column masks and commitment blinds

This canonical ordering places each column's suffix samples immediately before its blind.
The next column is constructed from the full masked row history. A tape equivalence
separates the row and blind subsequences without changing either order. `BatchedTape`
connects this representation to schedules that sample several tails before their blinds.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Split off the first scalar of a tape, keeping the remaining indices in order. -/
def firstTapeEquiv (length : ℕ) :
    (Fin (length + 1) → Fp) ≃ ((Fin 1 → Fp) × (Fin length → Fp)) where
  toFun tape := ((fun _ => tape 0), fun i => tape i.succ)
  invFun parts := Fin.cons (parts.1 0) parts.2
  left_inv tape := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv parts := by
    apply Prod.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rfl

/-- Count every suffix sample and the immediately following commitment blind. -/
def columnFullSampleCount {n : ℕ} : List (ColumnStep n) → ℕ
  | [] => 0
  | step :: rest => (n - step.firstMasked) + (1 + columnFullSampleCount rest)

/-- One independent commitment blind is added per constructed column. -/
theorem columnFullSampleCount_eq {n : ℕ} (steps : List (ColumnStep n)) :
    columnFullSampleCount steps = columnRowSampleCount steps + steps.length := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp only [columnFullSampleCount, columnRowSampleCount, List.length_cons, ih]; omega

/-- Separate row masks and commitment blinds from the canonical interleaved tape. -/
def columnCoinEquiv {n : ℕ} : (steps : List (ColumnStep n)) →
    (Fin (columnFullSampleCount steps) → Fp) ≃
      ((Fin (columnRowSampleCount steps) → Fp) × (Fin steps.length → Fp))
  | [] =>
    { toFun := fun _ => (Fin.elim0, Fin.elim0)
      invFun := fun _ => Fin.elim0
      left_inv := by intro tape; funext i; exact Fin.elim0 i
      right_inv := by intro parts; ext i <;> exact Fin.elim0 i }
  | step :: rest =>
    let A := Fin (n - step.firstMasked) → Fp
    let B := Fin 1 → Fp
    let C := Fin (columnRowSampleCount rest) → Fp
    let D := Fin rest.length → Fp
    let split := (splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp).trans
      (Equiv.prodCongr (Equiv.refl A) ((splitTapeEquiv 1 (columnFullSampleCount rest) Fp).trans
        (Equiv.prodCongr (Equiv.refl B) (columnCoinEquiv rest))))
    let regroup := (Equiv.prodAssoc A B (C × D)).symm.trans (Equiv.prodProdProdComm A B C D)
    let join := Equiv.prodCongr (splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp).symm
      (firstTapeEquiv rest.length).symm
    split.trans (regroup.trans join)

/-- The first column's suffix and blind are separated before recursing on the remaining tape. -/
theorem columnCoinEquiv_cons_apply {n : ℕ} (step : ColumnStep n) (rest : List (ColumnStep n))
    (tape : Fin (columnFullSampleCount (step :: rest)) → Fp) :
    columnCoinEquiv (step :: rest) tape =
      let first := splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp tape
      let next := splitTapeEquiv 1 (columnFullSampleCount rest) Fp first.2
      let later := columnCoinEquiv rest next.2
      ((splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp).symm (first.1, later.1),
        Fin.cons (next.1 0) later.2) := rfl

/-- Execute the canonical order: suffix, blind, then the next private construction. -/
def columnMaterialFromTape {n : ℕ} : (steps : List (ColumnStep n)) → ColumnHistory n →
    (Fin (columnFullSampleCount steps) → Fp) → (ColumnHistory n × (Fin steps.length → Fp))
  | [], _, _ => ([], Fin.elim0)
  | step :: rest, history, tape =>
    let first := splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp tape
    let next := splitTapeEquiv 1 (columnFullSampleCount rest) Fp first.2
    let row := columnRowsFromCoins step history first.1
    let later := columnMaterialFromTape rest (row :: history) next.2
    (row :: later.1, Fin.cons (next.1 0) later.2)

/-- The tape separation reproduces exactly the executable rows and every commitment blind. -/
theorem columnMaterialFromTape_eq {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (tape : Fin (columnFullSampleCount steps) → Fp) :
    columnMaterialFromTape steps history tape =
      (columnRowsFromTape steps history (columnCoinEquiv steps tape).1, (columnCoinEquiv steps tape).2) := by
  induction steps generalizing history with
  | nil => rfl
  | cons step rest ih =>
    simp only [columnMaterialFromTape, columnCoinEquiv_cons_apply]
    rw [ih]
    simp only [columnRowsFromTape, Equiv.apply_symm_apply]

/-- Uniform interleaved samples give the private row law and independent uniform blinds. -/
theorem uniformTapeColumnMaterial {n : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n) :
    (PMF.uniformOfFintype (Fin (columnFullSampleCount steps) → Fp)).map
        (columnMaterialFromTape steps history) =
      Zcash.independentProductPMF (idealColumnRows steps history)
        (PMF.uniformOfFintype (Fin steps.length → Fp)) := by
  have hfactor : columnMaterialFromTape steps history =
      (fun coins => (columnRowsFromTape steps history coins.1, coins.2)) ∘ columnCoinEquiv steps := by
    funext tape
    exact columnMaterialFromTape_eq steps history tape
  rw [hfactor, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform,
    Zcash.independentProductPMF_map_left _ _ (columnRowsFromTape steps history), uniformTapeColumnRows]

end Zcash.Snark.ZeroKnowledge
