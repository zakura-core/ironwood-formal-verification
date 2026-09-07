import Zcash.Snark.ZeroKnowledge.ColumnAttempt
import Zcash.Snark.ZeroKnowledge.PlonkRowConstruction

/-!
# Execute the concrete retained-row constructors on the pinned mask tape

This installs the advice, lookup-sort, and product-scan computations in the existing
22-column-per-Action schedule. Partial construction stops at the first sorting
failure and retains its private prefix. It reserves the same 126 replacement-row
samples per Action as the total schedule used by the joint simulation.

The successful-attempt theorem is an equality on the same tape, not a claim about
the distribution conditioned on success. The sampling comparison includes the
failure flag and prefix, but compares two samplers for the same witness-dependent
computation; it is not itself a zero-knowledge simulation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- The total comparison constructor, with failed lookup sorts explicitly replaced by zero. -/
def plonkTotalColumnConstructor {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (id : PrivateColumnId actions) (history : ColumnHistory 2048) : Fin 2048 → Fp :=
  (plonkConstructColumnResult vk pub witness ch id history).getD 0

/-- Install the partial retained-row computations in the exact private-column order. -/
def plonkColumnConstructionSteps {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp) :
    List (ColumnAttemptStep 2048) :=
  (privateColumnOrder actions).map fun id =>
    ⟨id.firstMasked, plonkConstructColumnResult vk pub witness ch id⟩

/-- The total comparison schedule is exactly the constructor accepted by the joint simulation. -/
theorem plonkColumnConstructionSteps_totalize {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp) :
    (plonkColumnConstructionSteps vk pub witness ch).map ColumnAttemptStep.totalize =
      plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch) := by
  simp only [plonkColumnConstructionSteps, List.map_map, Function.comp_def,
    ColumnAttemptStep.totalize, plonkColumnSteps]
  rfl

/-- The partial schedule reserves the original replacement-row tape budget. -/
theorem plonkColumnConstructionSteps_row_samples {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp) :
    columnRowSampleCount ((plonkColumnConstructionSteps vk pub witness ch).map ColumnAttemptStep.totalize) =
      126 * actions := by
  rw [plonkColumnConstructionSteps_totalize, plonkColumnSteps_row_samples]

/-- Run the concrete reference column construction from the empty history on its selected row tape. -/
def plonkColumnAttempt {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) : ColumnAttemptResult 2048 :=
  columnAttemptFromTape (plonkColumnConstructionSteps vk pub witness ch) []
    (tape ∘ Fin.cast (plonkColumnConstructionSteps_row_samples vk pub witness ch))

/-- The attempt completes exactly when all 22 private columns per Action were produced. -/
theorem plonkColumnAttempt_complete_iff {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    (plonkColumnAttempt vk pub witness ch tape).complete = true ↔
      (plonkColumnAttempt vk pub witness ch tape).columns.length = 22 * actions := by
  simpa only [plonkColumnAttempt, plonkColumnConstructionSteps, List.length_map, privateColumnOrder_length]
    using columnAttemptFromTape_complete_iff (plonkColumnConstructionSteps vk pub witness ch) []
      (tape ∘ Fin.cast (plonkColumnConstructionSteps_row_samples vk pub witness ch))

/-- Equal schedules give the same execution when supplied through their fixed-size tape casts. -/
theorem columnRowsFromTape_cast_eq {n count : ℕ} {steps steps' : List (ColumnStep n)}
    (hsteps : steps = steps') (hcount : columnRowSampleCount steps = count)
    (hcount' : columnRowSampleCount steps' = count) (history : ColumnHistory n)
    (tape : Fin count → Fp) :
    columnRowsFromTape steps history (tape ∘ Fin.cast hcount) =
      columnRowsFromTape steps' history (tape ∘ Fin.cast hcount') := by
  cases hsteps
  rfl

/-- Successful reference attempts agree exactly with the totalized joint-simulation rows. -/
theorem plonkColumnAttempt_eq_of_complete {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true) :
    (plonkColumnAttempt vk pub witness ch tape).columns =
      columnRowsFromTape (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness ch)) []
        (tape ∘ Fin.cast (plonkColumnSteps_row_samples (plonkTotalColumnConstructor vk pub witness ch))) := by
  have h := columnAttemptFromTape_eq_of_complete (plonkColumnConstructionSteps vk pub witness ch) []
    (tape ∘ Fin.cast (plonkColumnConstructionSteps_row_samples vk pub witness ch)) hcomplete
  exact h.trans (columnRowsFromTape_cast_eq (plonkColumnConstructionSteps_totalize vk pub witness ch)
    (plonkColumnConstructionSteps_row_samples vk pub witness ch)
    (plonkColumnSteps_row_samples (plonkTotalColumnConstructor vk pub witness ch)) [] tape)

/-- The entire reference attempt, including failure and private prefix, costs `126m` sample biases.

The right-hand law still uses the same private witness. This theorem does not condition
on completion or assert a public simulator for failed column construction. -/
theorem plonkColumnAttempt_sampling_error_bound {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp) :
    PMFEventBiasLE
      ((sampleFieldsWith (126 * actions) (plonkColumnAttempt vk pub witness ch)).runFreshPMF fieldSample)
      ((PMF.uniformOfFintype (Fin (126 * actions) → Fp)).map (plonkColumnAttempt vk pub witness ch))
      ((126 * actions : ℕ) * challenge255Bias) ∧
    PMFEventBiasLE
      ((PMF.uniformOfFintype (Fin (126 * actions) → Fp)).map (plonkColumnAttempt vk pub witness ch))
      ((sampleFieldsWith (126 * actions) (plonkColumnAttempt vk pub witness ch)).runFreshPMF fieldSample)
      ((126 * actions : ℕ) * challenge255Bias) :=
  sampleFieldsWith_error_bound (126 * actions) (plonkColumnAttempt vk pub witness ch)

end Zcash.Snark.ZeroKnowledge
