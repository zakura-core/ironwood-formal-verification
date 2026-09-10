import Zcash.Meta.AdviceSourceCertificate
import Zcash.Meta.SourceListCertificate
import Zcash.Meta.KernelRfl
import Zcash.Meta.AxiomCheck

/-!
# Source obligations across separately checked declarations

The tests split a parameterized program across ordinary declaration boundaries.
They check exact source erasure and reject attempts to close a nonempty remainder
with the empty certificate.
-/

namespace Zcash.Meta.Tests.SourceCertificatePiece

open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge

def source (row : ℕ) : List (PlacedAdviceProgram Fp × Option AdviceAddress) :=
  [(⟨⟨0⟩, row, instanceGet ⟨0⟩ row⟩, none),
   (⟨⟨1⟩, row, .ofFExpr (.expr (.of 0 row (⟨0⟩ : Column .advice)))⟩, none)]

def untouched (row : ℕ) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (source row) := by
  certify_source_advice_piece 0 1

def first (row : ℕ) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (source row) := by
  certify_source_advice_piece 8 1

def second (row : ℕ) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (first row).remaining := by
  certify_source_advice_piece 8 1

def complete (row : ℕ) : AdviceSourceCertificate (source row) :=
  (first row).finish ((second row).finish AdviceSourceCertificate.nil)

/-- Doing no work retains the whole source as an obligation, guarding the zero-step boundary. -/
theorem zeroSteps_retainsSource (row : ℕ) : (untouched row).remaining = source row := by
  kernel_rfl

/-- The first piece retains the second instruction, guarding against premature completion. -/
theorem first_retainsSuffix (row : ℕ) :
    (first row).remaining = (source row).drop 1 := by
  kernel_rfl

/-- Separate declarations preserve the exact original instructions and their copy tags. -/
theorem complete_erases (row : ℕ) :
    (complete row).annotations.map (fun entry => (entry.1.instruction, entry.2)) = source row :=
  (complete row).erases

/-- An untouched source or a proper prefix cannot be completed without its suffix. -/
theorem rejectsMissingSuffix : True := by
  fail_if_success
    have _invalid : AdviceSourceCertificate (source 7) :=
      (untouched 7).finish AdviceSourceCertificate.nil
  fail_if_success
    have _invalid : AdviceSourceCertificate (source 7) :=
      (first 7).finish AdviceSourceCertificate.nil
  trivial

def listFirst (value : ℕ) : SourceCertificatePiece SourceListCertificate [value, value + 1] := by
  certify_source_list_piece 8 1

def listSecond (value : ℕ) : SourceCertificatePiece SourceListCertificate (listFirst value).remaining := by
  certify_source_list_piece 8 1

def listComplete (value : ℕ) : SourceListCertificate [value, value + 1] :=
  (listFirst value).finish ((listSecond value).finish SourceListCertificate.nil)

/-- Metadata pieces preserve both the parameterized entries and their source order. -/
theorem listComplete_erases (value : ℕ) :
    (listComplete value).entries = [value, value + 1] :=
  (listComplete value).source_eq

/-- Metadata reflection cannot discard an unprocessed suffix when completing a certificate. -/
theorem listRejectsMissingSuffix : True := by
  fail_if_success
    have _invalid : SourceListCertificate [7, 8] :=
      (listFirst 7).finish SourceListCertificate.nil
  trivial

assert_computable Zcash.Meta.Tests.SourceCertificatePiece.source
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.untouched +choice
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.first +choice
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.second +choice
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.complete +choice
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.zeroSteps_retainsSource
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.first_retainsSuffix
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.complete_erases
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.rejectsMissingSuffix
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.listFirst
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.listSecond
assert_computable Zcash.Meta.Tests.SourceCertificatePiece.listComplete
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.listComplete_erases
assert_axioms Zcash.Meta.Tests.SourceCertificatePiece.listRejectsMissingSuffix

end Zcash.Meta.Tests.SourceCertificatePiece
