import Zcash.Snark.ZeroKnowledge.PlonkConstructedRows
import Zcash.Snark.ZeroKnowledge.PlonkPermutationRows

/-!
# The executed permutation scans satisfy the actual permutation constraints

The three set records and packed chunks of the honest constraint model are identified
with the existing deployed polynomial layout. The completed attempt supplies every
scan row, including the inherited seeds and retained terminal values. The seven
constraint polynomials then vanish on the domain outside zero denominators, given
the full packed-factor product identity.

Deriving that product identity from the actual copy wiring and supplied witness,
and bounding the exceptional events, remain separate obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial Finset

/-- The actual three-set/chunk model is exactly the deployed layout used by the scan theorem. -/
theorem plonkConstraintModel_permutation_polynomials {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (a : Fin actions)
    (hchunks : vk.permutationChunks.length = 3) :
    let z := finFn (fun s : Fin 3 => privateColumnPolynomial rows (.permutationProduct a s))
    let pairs := fun c => plonkPermutationPairPolynomials pub rows a (vk.permutationChunks.getD c [])
    (plonkConstraintModel vk pub ch rows).sets a =
      deployedPermSets (omegaOf 11) 3 z (permutationTerminalPolynomials z (omegaOf 11 ^ 2042)) ∧
    (plonkConstraintModel vk pub ch rows).chunks a =
      deployedPermChunks (omegaOf 11) 3 z (permutationTerminalPolynomials z (omegaOf 11 ^ 2042)) pairs := by
  let z := finFn (fun s : Fin 3 => privateColumnPolynomial rows (.permutationProduct a s))
  let pairs := fun c => plonkPermutationPairPolynomials pub rows a (vk.permutationChunks.getD c [])
  have hentry (i : ℕ) (hi : i < 3) :
      (plonkPolynomialClaimProof (k := k) (G := G) pub rows).permutationSetEvals a ⟨i, hi⟩ =
        permSetPolys (omegaOf 11) (z i) (permutationTerminalPolynomials z (omegaOf 11 ^ 2042) i) := by
    rw [plonkPolynomialClaimProof_permutationSetEvals]
    simp only [z, finFn, dif_pos hi, permutationTerminalPolynomials]
    rfl
  constructor
  · apply List.ext_getElem
    · simp [plonkConstraintModel, deployedPermSets]
      rfl
    · intro i hi hi'
      have hic : i < 3 := by simpa only [deployedPermSets, List.length_map, List.length_range] using hi'
      simpa only [plonkConstraintModel, List.getElem_ofFn, deployedPermSets,
        List.getElem_map, List.getElem_range] using hentry i hic
  · apply List.ext_getElem
    · simp [plonkConstraintModel, deployedPermChunks, hchunks]
      exact Nat.le_refl 3
    · intro i hi hi'
      have hic : i < 3 := by simpa only [deployedPermChunks, List.length_map, List.length_range] using hi'
      simp only [plonkConstraintModel, List.getElem_map, List.getElem_zip, List.getElem_ofFn,
        deployedPermChunks, List.getElem_range]
      apply Prod.ext
      · exact hentry i hic
      · change _ = plonkPermutationPairPolynomials pub rows a (vk.permutationChunks.getD i [])
        rw [List.getD_eq_getElem vk.permutationChunks [] (by omega)]
        rfl

/-- All seven permutation constraints of a completed attempt divide by the domain polynomial. -/
theorem plonkColumnAttempt_permutationConstraints_dvd {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hcomplete : (plonkColumnAttempt vk pub witness ch tape).complete = true)
    (a : Fin actions) (hchunks : vk.permutationChunks.length = 3)
    (hproduct :
      (∏ c ∈ range 3, ∏ i ∈ range 2042,
        permutationRowNumerator
          (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
          ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range 2042,
        permutationRowDenominator
          (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
          ch.beta ch.gamma c i)
    (hden : ∀ c < 3, ∀ i < 2042,
      permutationRowDenominator
        (plonkPermutationFactorRows pub (plonkColumnAttempt vk pub witness ch tape).columns a vk.permutationChunks)
        ch.beta ch.gamma c i ≠ 0) :
    let rows := (plonkColumnAttempt vk pub witness ch tape).columns
    ∀ poly ∈ (plonkConstraintModel vk pub ch rows).permutationConstraints a,
      (X ^ 2048 - 1 : CPoly) ∣ poly := by
  let rows := (plonkColumnAttempt vk pub witness ch tape).columns
  let z := finFn (fun s : Fin 3 => privateColumnPolynomial rows (.permutationProduct a s))
  let pairs := fun c => plonkPermutationPairPolynomials pub rows a (vk.permutationChunks.getD c [])
  have hz (c : ℕ) (hc : c < 3) (i : ℕ) (hi : i ≤ 2042) :
      (z c).eval (omegaOf 11 ^ i) =
        permutationScanRows (permutationPairRows (omegaOf 11) pairs)
          ch.beta ch.gamma (omegaOf 11) vk.delta vk.chunkLen 2042 c i := by
    simpa only [z, finFn, dif_pos hc] using
      plonkColumnAttempt_permutation_scan vk pub witness ch tape hcomplete a ⟨c, hc⟩ i hi
  have hdiv := permutationExpressions_dvd_domain_of_scan (n := 2048) (omegaOf 11)
    (by decide) (omegaOf_primitiveRoot 11 (by decide)) 2042 vk.chunkLen z pairs
    ch.beta ch.gamma vk.delta plonkSelectors plonkSelectors_eval_row hz hproduct hden
  have hlayout := plonkConstraintModel_permutation_polynomials vk pub ch rows a hchunks
  change ∀ poly ∈ (plonkConstraintModel vk pub ch rows).permutationConstraints a,
    (X ^ 2048 - 1 : CPoly) ∣ poly
  intro poly hpoly
  rw [ConstraintPolyModel.permutationConstraints_eq, hlayout.1, hlayout.2] at hpoly
  exact hdiv poly hpoly

end Zcash.Snark.ZeroKnowledge
