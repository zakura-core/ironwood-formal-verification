import Zcash.Meta.AdviceSourceCertificate
import Zcash.Meta.KernelRfl
import Zcash.Meta.AxiomCheck

/-!
# Adversarial checks for source-preserving read certificates

These checks cover omitted reads, unavailable reads, changed source addresses,
and a nested native callback. Generated annotations are proof-carrying data;
successful generation alone must not make either source equality or a finite
availability check succeed.
-/

namespace Zcash.Meta.Tests.AdviceSourceCertificate

open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge

/-- The actual nested initial-slope callback can retain a constant virtual y. -/
def nestedInitialSlope (generators : Specs.Sinsemilla.Generators)
    (piece x : AssignedCell Fp) (point : Point Fp)
    (last : Ecc.DoubleAndAddRow (AssignedCell Fp)) (next : AssignedCell Fp) :
    SupportedAdviceProgram Fp :=
  annotate_advice ⟨⟨0⟩, 0, Sinsemilla.HashPiece.initLWit generators piece x
    (if (0 : ℕ) = 0 then (fun _ => point.y) else Sinsemilla.Chain.boundaryYA last next)
    (fun row => row.1)⟩

/-- The native callback retains its two genuine reads despite its unused conditional branch. -/
theorem nestedInitialSlope_reads (generators : Specs.Sinsemilla.Generators)
    (piece x : AssignedCell Fp) (point : Point Fp)
    (last : Ecc.DoubleAndAddRow (AssignedCell Fp)) (next : AssignedCell Fp) :
    (nestedInitialSlope generators piece x point last next).reads = [piece, x] := by
  kernel_rfl

/-- An actual piece-cell read cannot be silently certified with an empty dependency list. -/
theorem rejectsOmittedRead (_piece : AssignedCell Fp) : True := by
  fail_if_success
    have _invalid : WitnessFunctionSupport []
        (fun env => ((Sinsemilla.HashPiece.zWit _piece 1).eval env)[0]) := by
      witness_read_support
  trivial

/-- A source can be annotated even when a later availability check must reject it. -/
def futureRead : AdviceSourceCertificate (F := Fp)
    [(⟨⟨0⟩, 0, .ofFExpr (.expr (.of 0 1 (⟨0⟩ : Column .advice)))⟩, none)] := by
  certify_source_advice

/-- The original row-one read is unavailable before the first row-zero write. -/
theorem futureRead_rejected :
    adviceSupportMapPlan id ∅ futureRead.readCertificate.annotations = false := by
  kernel_rfl

/-- Changing a target row does not preserve a certificate's source equation. -/
theorem rejectsChangedSource : True := by
  fail_if_success
    have _invalid : AdviceSourceCertificate (F := Fp)
        [(⟨⟨0⟩, 1, .ofFExpr (.expr (.of 0 1 (⟨0⟩ : Column .advice)))⟩, none)] := futureRead
  trivial

/-- Transport changes proof metadata while retaining directly evaluable annotation data. -/
theorem transport_retainsData
    {source target : List (PlacedAdviceProgram Fp × Option AdviceAddress)}
    (equality : source = target) (certificate : AdviceSourceCertificate source) :
    (certificate.transport equality).annotations = certificate.annotations := by
  kernel_rfl

assert_computable Zcash.Meta.Tests.AdviceSourceCertificate.nestedInitialSlope +choice
assert_axioms Zcash.Meta.Tests.AdviceSourceCertificate.nestedInitialSlope_reads
assert_axioms Zcash.Meta.Tests.AdviceSourceCertificate.rejectsOmittedRead
assert_computable Zcash.Meta.Tests.AdviceSourceCertificate.futureRead +choice
assert_axioms Zcash.Meta.Tests.AdviceSourceCertificate.futureRead_rejected
assert_axioms Zcash.Meta.Tests.AdviceSourceCertificate.rejectsChangedSource
assert_axioms Zcash.Meta.Tests.AdviceSourceCertificate.transport_retainsData

end Zcash.Meta.Tests.AdviceSourceCertificate
