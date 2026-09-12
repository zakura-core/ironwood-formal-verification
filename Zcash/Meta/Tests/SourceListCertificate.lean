import Zcash.Meta.SourceListCertificate
import Zcash.Meta.KernelRfl
import Zcash.Meta.AxiomCheck

/-! Exact source reflection across an opaque, parameterized metadata producer. -/

namespace Zcash.Meta.Tests.SourceListCertificate

open Zcash.Snark.ZeroKnowledge

-- Exercise checked piece composition across opaque equations and local parameters.
set_option Zcash.sourceCertificate.chunkSteps 2

def originalMetadata (row : ℕ) : List (ℕ × String) :=
  [(row, "range"), (row, "coordinates"), (row + 1, "tail")]

opaque packedMetadata : { producer : ℕ → List (ℕ × String) // producer = originalMetadata } :=
  ⟨originalMetadata, rfl⟩

noncomputable def reflectedMetadata (row : ℕ) :
    SourceListCertificate (packedMetadata.val row) := by
  certify_source_list

/-- Reflection retains the original labels and row offsets, checking that source certificates
preserve metadata. -/
theorem reflectedMetadata_entries (row : ℕ) :
    (reflectedMetadata row).entries =
      [(row, "range"), (row, "coordinates"), (row + 1, "tail")] := by
  kernel_rfl

/-- Changing a reflected label changes the certified list, guarding against metadata substitution. -/
theorem rejectsChangedLabel (row : ℕ) :
    (reflectedMetadata row).entries ≠
      [(row, "coordinates"), (row, "coordinates"), (row + 1, "tail")] := by
  rw [reflectedMetadata_entries]
  simp

/-- Reflection cannot reuse a certificate after its source label changes. -/
theorem rejectsChangedSource (_row : ℕ) : True := by
  fail_if_success
    have _invalid : SourceListCertificate
        [(_row, "coordinates"), (_row, "coordinates"), (_row + 1, "tail")] :=
      reflectedMetadata _row
  trivial

/-- Reflection rejects an abstract source without an equation exposing its entries. -/
theorem rejectsUnexposedSource (_source : List (ℕ × String)) : True := by
  fail_if_success
    have _invalid : SourceListCertificate _source := by certify_source_list
  trivial

/-- Transporting a source equality preserves its recorded entries, keeping subsequent scans
independent of equality casts. -/
theorem transport_retainsEntries (row : ℕ) :
    (SourceListCertificate.transport
      (congrFun packedMetadata.property row) (reflectedMetadata row)).entries =
      (reflectedMetadata row).entries := rfl

opaque packedStep (row : ℕ) :
    { step : ℕ × List (ℕ × String) × ℕ //
      step = (row, [(row, "range"), (row, "coordinates")], row + 1) } :=
  ⟨_, rfl⟩

/-- The next source call depends on an earlier opaque result and both lists are mapped. -/
noncomputable def reflectedThreadedMetadata (row : ℕ) :
    SourceListCertificate
      (((packedStep row).val.2.1 ++
        (packedStep (packedStep row).val.2.2).val.2.1).map
          fun entry => (entry.1, entry.2, (packedStep row).val.1)) := by
  certify_source_list

/-- Reflection preserves row state threaded between source calls, checking metadata from sequential
composition. -/
theorem reflectedThreadedMetadata_entries (row : ℕ) :
    (reflectedThreadedMetadata row).entries =
      [(row, "range", row), (row, "coordinates", row),
        (row + 1, "range", row), (row + 1, "coordinates", row)] := by
  kernel_rfl

assert_computable Zcash.Meta.Tests.SourceListCertificate.originalMetadata
assert_axioms Zcash.Meta.Tests.SourceListCertificate.packedMetadata
assert_axioms Zcash.Meta.Tests.SourceListCertificate.reflectedMetadata
assert_axioms Zcash.Meta.Tests.SourceListCertificate.reflectedMetadata_entries
assert_axioms Zcash.Meta.Tests.SourceListCertificate.rejectsChangedLabel
assert_axioms Zcash.Meta.Tests.SourceListCertificate.rejectsChangedSource
assert_axioms Zcash.Meta.Tests.SourceListCertificate.rejectsUnexposedSource
assert_axioms Zcash.Meta.Tests.SourceListCertificate.transport_retainsEntries
assert_axioms Zcash.Meta.Tests.SourceListCertificate.packedStep
assert_axioms Zcash.Meta.Tests.SourceListCertificate.reflectedThreadedMetadata
assert_axioms Zcash.Meta.Tests.SourceListCertificate.reflectedThreadedMetadata_entries

end Zcash.Meta.Tests.SourceListCertificate
