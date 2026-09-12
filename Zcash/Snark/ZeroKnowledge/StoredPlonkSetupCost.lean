import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Arithmetic.Group

/-!
# Stored public parameters and concrete setup readers

The simulator input stores the generator vector and fixed/sigma row matrices as
lists. Encoding a specified setup gives an exact representation theorem; the
runtime bounds concern reads of this supplied stored setup. Parameter generation
is not part of those input-reader bounds.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp URS)
set_option maxRecDepth 10000

/-- The materialized public vectors required by the eleven-round reference prover. -/
structure StoredPlonkSetup (G : Type*) where
  generators : List G
  w : G
  u : G
  fixedRows : List (List Fp)
  sigmaRows : List (List Fp)

/-- Store the specified finite public vectors in their original index order. -/
def StoredPlonkSetup.encode {G : Type*} (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) : StoredPlonkSetup G where
  generators := List.ofFn generators
  w := w
  u := u
  fixedRows := List.ofFn (fun column => List.ofFn (fixed column))
  sigmaRows := List.ofFn (fun column => List.ofFn (sigma column))

/-- Interpret the stored reference string with the original identity default for absent points. -/
def StoredPlonkSetup.urs {G : Type*} [Zero G] (stored : StoredPlonkSetup G) : URS G where
  k := 11
  g := fun index => stored.generators.getD index.val 0
  w := stored.w
  u := stored.u

/-- Read a materialized generator, retaining the full traversal to its position. -/
def StoredPlonkSetup.generatorCosted {G : Type*} [Zero G] (stored : StoredPlonkSetup G)
    (read : ℕ) (index : Fin 2048) : G × ℕ :=
  getDListCosted read 0 stored.generators index.val

/-- Read a materialized fixed-column row with both list traversals counted. -/
def StoredPlonkSetup.fixedCosted {G : Type*} (stored : StoredPlonkSetup G)
    (read : ℕ) (column : Fin 29) (row : Fin 2048) : Fp × ℕ :=
  storedMatrixEntryCosted read 0 stored.fixedRows column.val row.val

/-- Read a materialized permutation-label row with both list traversals counted. -/
def StoredPlonkSetup.sigmaCosted {G : Type*} (stored : StoredPlonkSetup G)
    (read : ℕ) (column : Fin 15) (row : Fin 2048) : Fp × ℕ :=
  storedMatrixEntryCosted read 0 stored.sigmaRows column.val row.val

/-- Stored generator reads reproduce the specified finite generator vector. -/
theorem StoredPlonkSetup.generatorCosted_encode_result {G : Type*} [Zero G]
    (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (index : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).generatorCosted read index).1 = generators index := by
  have hi : index.val < (List.ofFn generators).length := by simpa only [List.length_ofFn] using index.isLt
  simp only [generatorCosted, encode, getDListCosted_result, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

/-- Encoding and interpreting the parameters preserves the entire original reference string. -/
theorem StoredPlonkSetup.urs_encode {G : Type*} [Zero G] (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    (StoredPlonkSetup.encode generators w u fixed sigma).urs =
      { k := 11, g := generators, w := w, u := u } := by
  have hg : (fun index : Fin 2048 => (List.ofFn generators).getD index.val 0) = generators := by
    funext index
    have hi : index.val < (List.ofFn generators).length := by simpa only [List.length_ofFn] using index.isLt
    rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  dsimp only [urs, encode]
  exact congrArg (fun values : Fin 2048 → G => ({ k := 11, g := values, w := w, u := u } : URS G)) hg

/-- Stored fixed rows reproduce every specified fixed-column entry. -/
theorem StoredPlonkSetup.fixedCosted_encode_result {G : Type*} (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (column : Fin 29) (row : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).fixedCosted read column row).1 = fixed column row :=
  storedMatrixEntryCosted_ofFn read 0 fixed column row

/-- Stored sigma rows reproduce every specified permutation-label entry. -/
theorem StoredPlonkSetup.sigmaCosted_encode_result {G : Type*} (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (column : Fin 15) (row : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).sigmaCosted read column row).1 = sigma column row :=
  storedMatrixEntryCosted_ofFn read 0 sigma column row

/-- The concrete generator access bound follows from the 2048 stored points. -/
theorem StoredPlonkSetup.generatorCosted_encode_cost_le {G : Type*} [Zero G]
    (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (index : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).generatorCosted read index).2 ≤ 4097 + read := by
  have h := getDListCosted_cost_le read (0 : G) (List.ofFn generators) index.val
  simp only [List.length_ofFn] at h
  dsimp only [generatorCosted, encode]
  omega

/-- The fixed-row access bound follows from the actual 29 by 2048 stored matrix. -/
theorem StoredPlonkSetup.fixedCosted_encode_cost_le {G : Type*} (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (column : Fin 29) (row : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).fixedCosted read column row).2 ≤ 4157 + 2 * read := by
  have h := storedMatrixEntryCosted_cost_le read (0 : Fp)
    (List.ofFn (fun index => List.ofFn (fixed index))) column.val row.val 2048 (fun values hmem => by
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hmem
      simp only [List.length_ofFn, le_refl])
  simp only [List.length_ofFn] at h
  dsimp only [fixedCosted, encode]
  omega

/-- The sigma-row access bound follows from the actual 15 by 2048 stored matrix. -/
theorem StoredPlonkSetup.sigmaCosted_encode_cost_le {G : Type*} (generators : Fin 2048 → G) (w u : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (read : ℕ) (column : Fin 15) (row : Fin 2048) :
    ((StoredPlonkSetup.encode generators w u fixed sigma).sigmaCosted read column row).2 ≤ 4129 + 2 * read := by
  have h := storedMatrixEntryCosted_cost_le read (0 : Fp)
    (List.ofFn (fun index => List.ofFn (sigma index))) column.val row.val 2048 (fun values hmem => by
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hmem
      simp only [List.length_ofFn, le_refl])
  simp only [List.length_ofFn] at h
  dsimp only [sigmaCosted, encode]
  omega

end Zcash.Snark.ZeroKnowledge
