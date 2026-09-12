import Zcash.Arithmetic.CommitLagrange
import Zcash.Snark.Core.Vesta
import Zcash.Common.DiscreteLogRelation

/-!
# Group arithmetic for captured prover executions

The existing Vesta kernel evaluates scalar multiplications and vector commitments.
These equalities connect it to the protocol's group operations for every input;
the fixture replay selects the implementations explicitly.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic
open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective

/-- Evaluate a scalar multiplication with the existing canonical-coordinate kernel. -/
def scale (scalar : Fp) (point : VestaG) : VestaG :=
  NatKernel.toG (NatKernel.pnsmul scalar.val (ofPVes (PVes.ofAffine point)))

/-- Kernel multiplication computes the same field action used in the IPA equations. -/
theorem scale_result (scalar : Fp) (point : VestaG) : scale scalar point = scalar • point := by
  unfold scale
  rw [NatKernel.toG_eq, Function.comp_apply,
    (NatKernel.pnsmul_spec (valid_toPVes_ofPVes_ofAffine point) scalar.val
      (val_lt_two_pow_256 scalar)).2,
    toPVes_ofPVes, PVes.toAffine_ofAffine]
  rw [← Nat.cast_smul_eq_nsmul Fp scalar.val point, ZMod.natCast_rightInverse scalar]

/-- Commit to a finite coefficient vector using the proved windowed multi-scalar multiplication. -/
def commitVector {n : ℕ} (generators : Fin n → VestaG) (coefficients : Fin n → Fp) : VestaG :=
  commitNatPre 8 0 ((List.ofFn generators).map fun g => ofPVes (PVes.ofAffine g))
    (List.ofFn coefficients)

/-- Every vector commitment agrees with the reference sum, including zero coefficients and points. -/
theorem commitVector_result {n : ℕ} (generators : Fin n → VestaG)
    (coefficients : Fin n → Fp) : commitVector generators coefficients = commitGen generators coefficients := by
  rw [commitVector, commitNatPre_eq 8 (by decide) 0 (List.ofFn generators)
    (List.ofFn coefficients) (by simp)]
  unfold Msm.commitLagrangeSpec commitGen
  simp only [List.length_ofFn, add_zero]
  change (∑ i ∈ Finset.range n,
    ((List.ofFn coefficients).getD i 0).val • (List.ofFn generators).getD i 0) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem _ 0 (by simp), List.getD_eq_getElem _ 0 (by simp)]
  simp only [List.getElem_ofFn]
  rw [← Nat.cast_smul_eq_nsmul Fp (coefficients i).val (generators i),
    ZMod.natCast_rightInverse (coefficients i)]

end Zcash.Snark.Fixtures.Prover
