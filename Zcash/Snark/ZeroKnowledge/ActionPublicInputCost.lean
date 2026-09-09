import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.ActionPublicData

/-!
# Stored Action public inputs and concrete instance-row access

The input is a materialized list of the original ten-field Action records.
Serialization charges every field projection and output cell. The concrete
row reader retains that preparation and both list traversals, and its result
is the original compiler public-input layout with zero padding.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Circuits.Action

/-- Copy the ten original fields in row order, paying for every projection and list cell. -/
def actionPublicInputElementsCosted (input : PublicInputs Fp × ℕ) : List Fp × ℕ :=
  ([input.1.anchor, input.1.cvX, input.1.cvY, input.1.nfOld, input.1.rkX,
    input.1.rkY, input.1.cmx, input.1.enableSpend, input.1.enableOutput,
    input.1.disableCrossAddress], input.2 + 21)

/-- The stored row order is exactly the circuit's public-input serialization. -/
theorem actionPublicInputElementsCosted_result (input : PublicInputs Fp × ℕ) :
    (actionPublicInputElementsCosted input).1 = (toElements input.1).toList := rfl

/-- Every original public-input field is materialized. -/
theorem actionPublicInputElementsCosted_length (input : PublicInputs Fp × ℕ) :
    (actionPublicInputElementsCosted input).1.length = 10 := rfl

/-- Serialization retains the whole input-record access and its twenty-one structural steps. -/
theorem actionPublicInputElementsCosted_cost (input : PublicInputs Fp × ℕ) :
    (actionPublicInputElementsCosted input).2 = input.2 + 21 := rfl

/-- Materialize the complete public instance matrix from stored Action records. -/
def actionPublicInputRowsCosted (inputs : List (PublicInputs Fp)) : List (List Fp) × ℕ :=
  mapListCosted (fun input => actionPublicInputElementsCosted (input, 1)) inputs

/-- Matrix construction preserves the supplied Action record order and every original field. -/
theorem actionPublicInputRowsCosted_result (inputs : List (PublicInputs Fp)) :
    (actionPublicInputRowsCosted inputs).1 = inputs.map (fun input => (toElements input).toList) := by
  simp only [actionPublicInputRowsCosted, mapListCosted_result, actionPublicInputElementsCosted_result]

/-- Exactly one instance row vector is produced for each stored Action record. -/
theorem actionPublicInputRowsCosted_length (inputs : List (PublicInputs Fp)) :
    (actionPublicInputRowsCosted inputs).1.length = inputs.length := by
  simp only [actionPublicInputRowsCosted_result, List.length_map]

/-- Every produced row vector contains precisely the ten supplied public fields. -/
theorem actionPublicInputRowsCosted_rowLength (inputs : List (PublicInputs Fp))
    (row : List Fp) (hmem : row ∈ (actionPublicInputRowsCosted inputs).1) : row.length = 10 := by
  simp only [actionPublicInputRowsCosted, mapListCosted_result, List.mem_map] at hmem
  obtain ⟨input, _, rfl⟩ := hmem
  exact actionPublicInputElementsCosted_length (input, 1)

/-- All record accesses, field copies, and matrix output cells have a linear total bound. -/
theorem actionPublicInputRowsCosted_cost_le (inputs : List (PublicInputs Fp)) :
    (actionPublicInputRowsCosted inputs).2 ≤ inputs.length * 23 + 1 := by
  exact mapListCosted_cost_le _ _ 22 (fun _ _ => le_rfl)

/-- The stored matrix recovers the actual Action instance rows, including all padded domain rows. -/
theorem actionPublicInputRowsCosted_instanceRows (inputs : List (PublicInputs Fp))
    (action : Fin inputs.length) (row : Fin 2048) :
    (((actionPublicInputRowsCosted inputs).1).getD action.val []).getD row.val 0 =
      actionInstanceRows (fun index : Fin inputs.length => inputs[index.val]) action row := by
  rw [actionPublicInputRowsCosted_result, actionInstanceRows_eq_elements]
  have haction : action.val < (inputs.map (fun input => (toElements input).toList)).length := by
    simpa only [List.length_map] using action.isLt
  rw [List.getD_eq_getElem _ _ haction, List.getElem_map]

/-- A complete concrete row reader, retaining public-record serialization and both list reads. -/
def actionStoredInstanceRowCosted (read : ℕ) (inputs : List (PublicInputs Fp))
    (action : Fin inputs.length) (row : Fin 2048) : Fp × ℕ :=
  let stored := actionPublicInputRowsCosted inputs
  let value := storedMatrixEntryCosted read 0 stored.1 action.val row.val
  (value.1, stored.2 + value.2 + 1)

/-- The concrete reader is exactly the original Action public-input row function. -/
theorem actionStoredInstanceRowCosted_result (read : ℕ) (inputs : List (PublicInputs Fp))
    (action : Fin inputs.length) (row : Fin 2048) :
    (actionStoredInstanceRowCosted read inputs action row).1 =
      actionInstanceRows (fun index : Fin inputs.length => inputs[index.val]) action row := by
  simp only [actionStoredInstanceRowCosted, storedMatrixEntryCosted_result]
  exact actionPublicInputRowsCosted_instanceRows inputs action row

/-- The actual row-provider bound follows from stored input size, with no callback-cost premise. -/
theorem actionStoredInstanceRowCosted_cost_le (read : ℕ) (inputs : List (PublicInputs Fp))
    (action : Fin inputs.length) (row : Fin 2048) :
    (actionStoredInstanceRowCosted read inputs action row).2 ≤ 25 * inputs.length + 2 * read + 25 := by
  have hp := actionPublicInputRowsCosted_cost_le inputs
  have hr := storedMatrixEntryCosted_cost_le read (0 : Fp) (actionPublicInputRowsCosted inputs).1
    action.val row.val 10 (fun values hmem => (actionPublicInputRowsCosted_rowLength inputs values hmem).le)
  rw [actionPublicInputRowsCosted_length] at hr
  simp only [actionStoredInstanceRowCosted]
  omega

end Zcash.Snark.ZeroKnowledge
