import Zcash.Snark.ZeroKnowledge.PermutationRowConstraints
import Zcash.Snark.ZeroKnowledge.DomainDivisibility
import Zcash.Snark.Soundness.Argument.PermutationRows

/-!
# The computed permutation scans give exact polynomial constraints

The existing permutation builder and deployed set/chunk layout are used unchanged.
Polynomial evaluation supplies next-row rotations and the first-row read of each
terminal rotation. The three-chunk row theorem then makes every constraint vanish
on the domain, deriving exact division from the scan and full product identity.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial Finset

/-- The first two chunks disclose their terminal rotation; the third does not. -/
def permutationTerminalPolynomials (z : ℕ → CPoly) (factor : Fp) (chunk : ℕ) : Option CPoly :=
  if chunk < 2 then some ((z chunk).comp (C factor * X)) else none

/-- Evaluate the routed column/sigma pairs at each row. -/
def permutationPairRows (omega : Fp) (pairs : ℕ → List (CPoly × CPoly)) (chunk row : ℕ) :
    List (Fp × Fp) := (pairs chunk).map (fun p => (p.1.eval (omega ^ row), p.2.eval (omega ^ row)))

/-- All seven actual polynomial constraints evaluate to zero by the computed three-chunk scan. -/
theorem permutationExpressions_eval_row_zero_of_scan
    (omega : Fp) (usable row chunkLen : ℕ) (z : ℕ → CPoly) (pairs : ℕ → List (CPoly × CPoly))
    (beta gamma delta : Fp) (selectors : CPoly × CPoly × CPoly)
    (hselectors : (selectors.1.eval (omega ^ row), selectors.2.1.eval (omega ^ row),
      selectors.2.2.eval (omega ^ row)) = rowSelectorValues (F := Fp) usable row)
    (hz : ∀ c < 3, ∀ i ≤ usable, (z c).eval (omega ^ i) =
      permutationScanRows (permutationPairRows omega pairs) beta gamma omega delta chunkLen usable c i)
    (hproduct : (∏ c ∈ range 3, ∏ i ∈ range usable,
        permutationRowNumerator (permutationPairRows omega pairs) beta gamma omega delta chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range usable,
        permutationRowDenominator (permutationPairRows omega pairs) beta gamma c i)
    (hden : ∀ c < 3, ∀ i < usable,
      permutationRowDenominator (permutationPairRows omega pairs) beta gamma c i ≠ 0) :
    (permutationExpressions
      (deployedPermSets omega 3 z (permutationTerminalPolynomials z (omega ^ usable)))
      (deployedPermChunks omega 3 z (permutationTerminalPolynomials z (omega ^ usable)) pairs)
      (C beta) (C gamma) X (C delta) chunkLen selectors.1 selectors.2.1 selectors.2.2).map
        (fun poly => poly.eval (omega ^ row)) = List.replicate 7 0 := by
  have h0 := congrArg Prod.fst hselectors
  have hlast := congrArg (fun s : Fp × Fp × Fp => s.2.1) hselectors
  have hblind := congrArg (fun s : Fp × Fp × Fp => s.2.2) hselectors
  dsimp only at h0 hlast hblind
  have hmap := permutationExpressions_map (evalRingHom (omega ^ row))
    (deployedPermSets omega 3 z (permutationTerminalPolynomials z (omega ^ usable)))
    (deployedPermChunks omega 3 z (permutationTerminalPolynomials z (omega ^ usable)) pairs)
    (C beta) (C gamma) X (C delta) chunkLen selectors.1 selectors.2.1 selectors.2.2
  simp only [coe_evalRingHom, eval_C, eval_X] at hmap
  rw [hmap, h0, hlast, hblind]
  apply permutationExpressions_zero_of_scan (permutationPairRows omega pairs)
    beta gamma omega delta chunkLen usable row (fun c i => (z c).eval (omega ^ i))
    (fun c i => ((z c).comp (C omega * X)).eval (omega ^ i))
    (fun c i => ((z c).comp (C (omega ^ usable) * X)).eval (omega ^ i)) hz ?_ ?_ hproduct hden
  · intro c _ i _
    exact eval_permSetPolys_nextEval omega (z c) none i
  · intro c _
    simp only [pow_zero, eval_comp_C_mul_X, _root_.mul_one]

/-- The scan and product identity give exact domain division for every permutation constraint. -/
theorem permutationExpressions_dvd_domain_of_scan {n : ℕ}
    (omega : Fp) (hn : 0 < n) (hroot : IsPrimitiveRoot omega n)
    (usable chunkLen : ℕ) (z : ℕ → CPoly) (pairs : ℕ → List (CPoly × CPoly))
    (beta gamma delta : Fp) (selectors : CPoly × CPoly × CPoly)
    (hselectors : ∀ row : Fin n,
      (selectors.1.eval (omega ^ row.val), selectors.2.1.eval (omega ^ row.val),
        selectors.2.2.eval (omega ^ row.val)) = rowSelectorValues (F := Fp) usable row.val)
    (hz : ∀ c < 3, ∀ i ≤ usable, (z c).eval (omega ^ i) =
      permutationScanRows (permutationPairRows omega pairs) beta gamma omega delta chunkLen usable c i)
    (hproduct : (∏ c ∈ range 3, ∏ i ∈ range usable,
        permutationRowNumerator (permutationPairRows omega pairs) beta gamma omega delta chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range usable,
        permutationRowDenominator (permutationPairRows omega pairs) beta gamma c i)
    (hden : ∀ c < 3, ∀ i < usable,
      permutationRowDenominator (permutationPairRows omega pairs) beta gamma c i ≠ 0) :
    ∀ poly ∈ permutationExpressions
      (deployedPermSets omega 3 z (permutationTerminalPolynomials z (omega ^ usable)))
      (deployedPermChunks omega 3 z (permutationTerminalPolynomials z (omega ^ usable)) pairs)
      (C beta) (C gamma) X (C delta) chunkLen selectors.1 selectors.2.1 selectors.2.2,
        (X ^ n - 1 : CPoly) ∣ poly := by
  intro poly hpoly
  apply domainPolynomial_dvd_of_rows omega hn hroot poly
  intro row
  have hzero := permutationExpressions_eval_row_zero_of_scan omega usable row.val chunkLen z pairs
    beta gamma delta selectors (hselectors row) hz hproduct hden
  have hmem := List.mem_map_of_mem (f := fun q : CPoly => q.eval (omega ^ row.val)) hpoly
  rw [hzero] at hmem
  exact List.eq_of_mem_replicate hmem

end Zcash.Snark.ZeroKnowledge
