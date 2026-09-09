import Zcash.Snark.ZeroKnowledge.DenseRootDivision
import Zcash.Snark.ZeroKnowledge.DistinctListCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- A distinct factor list is precisely the source's finite-set vanishing polynomial. -/
theorem denseRootDivisor_nodup (roots : List Fp) (hroots : roots.Nodup) :
    denseRootDivisor roots = vanishingProd roots.toFinset :=
  (List.prod_toFinset (fun root => CPolynomial.X - CPolynomial.C root) hroots).symm

/-- Counted division by the source's deduplicated point set, retaining every equality scan. -/
def denseDivVanishingCosted (equal read add multiply : ℕ) (roots values : List Fp) : List Fp × ℕ :=
  let points := distinctListCosted equal roots
  let result := denseDivRootsCosted read add multiply points.1 values
  (result.1, points.2 + result.2 + 1)

/-- Every repeated-point pattern gives the exact existing finite-set divisor and quotient. -/
theorem denseDivVanishingCosted_result (equal read add multiply : ℕ) (roots values : List Fp) :
    densePolynomial (denseDivVanishingCosted equal read add multiply roots values).1 =
      (densePolynomial values).div (vanishingProd roots.toFinset) := by
  rw [denseDivVanishingCosted, denseDivRootsCosted_result,
    denseRootDivisor_nodup _ (distinctListCosted_nodup equal roots), distinctListCosted_toFinset]

/-- Deduplication and all divisions preserve the stored polynomial's input width. -/
theorem denseDivVanishingCosted_length (equal read add multiply : ℕ) (roots values : List Fp) :
    (denseDivVanishingCosted equal read add multiply roots values).1.length = values.length :=
  denseDivRootsCosted_length _ _ _ _ _

/-- Full finite-set division cost includes duplicates, root reads, and every coefficient pass. -/
theorem denseDivVanishingCosted_cost_le (equal read add multiply : ℕ) (roots values : List Fp) :
    (denseDivVanishingCosted equal read add multiply roots values).2 ≤
      roots.length * roots.length * (equal + 2) +
        roots.length * (values.length * (read + add + multiply + 5) + read + 9) + 3 := by
  have hp := distinctListCosted_cost_le equal roots
  have hn := distinctListCosted_length_le equal roots
  have hd : (denseDivRootsCosted read add multiply (distinctListCosted equal roots).1 values).2 ≤
      roots.length * (values.length * (read + add + multiply + 5) + read + 5) + 1 := by
    rw [denseDivRootsCosted_cost]
    gcongr
  change (distinctListCosted equal roots).2 +
    (denseDivRootsCosted read add multiply (distinctListCosted equal roots).1 values).2 + 1 ≤ _
  calc
    _ ≤ (roots.length * roots.length * (equal + 2) + 4 * roots.length + 1) +
        (roots.length * (values.length * (read + add + multiply + 5) + read + 5) + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hp hd) 1
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
