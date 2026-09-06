import Zcash.Snark.Soundness.Argument.RunningProduct
import Mathlib.Data.List.OfFn

/-!
# Honest running-product rows, including zero denominators

The ordered scan uses the field's total inverse, with `0⁻¹ = 0`. Its product-ratio
formula holds even on exceptional
inputs. The required row recurrence can fail only at a zero denominator, and the
precise failure condition is retained. A permutation identity still forces the
terminal value to be zero or one, without requiring all denominators to be nonzero.

The same scan supplies lookup products and chained permutation products. The lookup
terminal identity is derived from permutations of the input and table prefixes.
Correctness of the concrete sorting algorithm, the permutation-column identity,
and integration of these rows into the joint prover experiment remain separate.
The zero-preserving fallback was inspected in the available Bento source at
`e32e61eb35b6e5b5e0600cb0903adcfe0cd617d8`; the pinned Sensei commit is still unlocated.
-/

namespace Zcash.Snark.ZeroKnowledge

open Finset

variable {F : Type*} [Field F]

/-- The exclusive ratio scan; a zero denominator contributes a zero inverse. -/
def runningProductRows (num den : ℕ → F) (initial : F) : ℕ → F
  | 0 => initial
  | i + 1 => runningProductRows num den initial i * num i / den i

/-- The first row is the supplied initial state. -/
theorem runningProductRows_zero (num den : ℕ → F) (initial : F) :
    runningProductRows num den initial 0 = initial := rfl

/-- One step computes the exact numerator/denominator ratio, including division by zero. -/
theorem runningProductRows_succ (num den : ℕ → F) (initial : F) (i : ℕ) :
    runningProductRows num den initial (i + 1) =
      runningProductRows num den initial i * num i / den i := rfl

/-- The closed prefix-product ratio holds with total inversion, without nonzero premises. -/
theorem runningProductRows_eq_ratio (num den : ℕ → F) (initial : F) (m : ℕ) :
    runningProductRows num den initial m =
      initial * (∏ i ∈ range m, num i) / (∏ i ∈ range m, den i) := by
  induction m with
  | zero => simp [runningProductRows]
  | succ m ih =>
    rw [runningProductRows_succ, ih, prod_range_succ, prod_range_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- A nonzero denominator makes the computed row satisfy the verifier's multiplicative check. -/
theorem runningProductRows_recurrence (num den : ℕ → F) (initial : F) (i : ℕ)
    (hden : den i ≠ 0) :
    runningProductRows num den initial (i + 1) * den i =
      runningProductRows num den initial i * num i := by
  rw [runningProductRows_succ, div_mul_cancel₀ _ hden]

/-- A row check fails exactly when its denominator is zero but its required right side is not. -/
theorem runningProductRows_violation_iff (num den : ℕ → F) (initial : F) (i : ℕ) :
    runningProductRows num den initial (i + 1) * den i ≠
        runningProductRows num den initial i * num i ↔
      den i = 0 ∧ runningProductRows num den initial i * num i ≠ 0 := by
  by_cases hden : den i = 0
  · simp only [hden, mul_zero, true_and]
    exact ne_comm
  · rw [runningProductRows_recurrence num den initial i hden]
    simp [hden]

/-- A zero denominator makes every later state zero. -/
theorem runningProductRows_zero_after_den_zero (num den : ℕ → F) (initial : F)
    (i m : ℕ) (him : i < m) (hden : den i = 0) :
    runningProductRows num den initial m = 0 := by
  have hprod : (∏ j ∈ range m, den j) = 0 :=
    prod_eq_zero (mem_range.mpr him) hden
  rw [runningProductRows_eq_ratio, hprod, div_zero]

/-- Equal numerator and denominator products give either zero or the initial terminal state. -/
theorem runningProductRows_end (num den : ℕ → F) (initial : F) (m : ℕ)
    (heq : (∏ i ∈ range m, num i) = ∏ i ∈ range m, den i) :
    runningProductRows num den initial m = 0 ∨ runningProductRows num den initial m = initial := by
  rw [runningProductRows_eq_ratio, heq]
  by_cases hd : (∏ i ∈ range m, den i) = 0
  · exact Or.inl (by rw [hd, div_zero])
  · exact Or.inr (by rw [mul_div_assoc, div_self hd, mul_one])

/-- With nonzero denominators, equal products return the unit initial state exactly. -/
theorem runningProductRows_end_one (num den : ℕ → F) (m : ℕ)
    (heq : (∏ i ∈ range m, num i) = ∏ i ∈ range m, den i)
    (hden : ∀ i < m, den i ≠ 0) : runningProductRows num den 1 m = 1 := by
  rw [runningProductRows_eq_ratio, one_mul, heq]
  exact div_self (prod_ne_zero_iff.mpr fun i hi => hden i (mem_range.mp hi))

/-- The terminal `z²-z` check holds even on zero-denominator executions. -/
theorem runningProductRows_terminal_constraint (num den : ℕ → F) (m : ℕ)
    (heq : (∏ i ∈ range m, num i) = ∏ i ∈ range m, den i) :
    runningProductRows num den 1 m ^ 2 - runningProductRows num den 1 m = 0 := by
  rcases runningProductRows_end num den 1 m heq with h | h <;> simp [h]

/-- Each permutation chunk starts from the preceding chunk's terminal state. -/
def chainedProductInitial (num den : ℕ → ℕ → F) (rows : ℕ) : ℕ → F
  | 0 => 1
  | chunk + 1 => runningProductRows (num chunk) (den chunk)
      (chainedProductInitial num den rows chunk) rows

/-- The rows of one chunk, with the actual inherited initial state. -/
def chainedProductRows (num den : ℕ → ℕ → F) (rows chunk : ℕ) : ℕ → F :=
  runningProductRows (num chunk) (den chunk) (chainedProductInitial num den rows chunk)

/-- The first permutation chunk starts at one. -/
theorem chainedProductRows_start (num den : ℕ → ℕ → F) (rows : ℕ) :
    chainedProductRows num den rows 0 0 = 1 := rfl

/-- Consecutive chunks satisfy the exact boundary-link check. -/
theorem chainedProductRows_chain (num den : ℕ → ℕ → F) (rows chunk : ℕ) :
    chainedProductRows num den rows (chunk + 1) 0 = chainedProductRows num den rows chunk rows := rfl

/-- Chaining row scans is the same ratio scan over whole-chunk products, including zeros. -/
theorem chainedProductInitial_eq_running (num den : ℕ → ℕ → F) (rows chunk : ℕ) :
    chainedProductInitial num den rows chunk =
      runningProductRows (fun c => ∏ i ∈ range rows, num c i)
        (fun c => ∏ i ∈ range rows, den c i) 1 chunk := by
  induction chunk with
  | zero => rfl
  | succ chunk ih =>
    rw [chainedProductInitial, runningProductRows_eq_ratio, ih, runningProductRows_succ]

/-- The inherited initial state preserves the row recurrence outside zero denominators. -/
theorem chainedProductRows_recurrence (num den : ℕ → ℕ → F) (rows chunk i : ℕ)
    (hden : den chunk i ≠ 0) :
    chainedProductRows num den rows chunk (i + 1) * den chunk i =
      chainedProductRows num den rows chunk i * num chunk i :=
  runningProductRows_recurrence _ _ _ i hden

/-- A whole-permutation product identity gives the final chunk's Boolean terminal value. -/
theorem chainedProductRows_terminal_constraint (num den : ℕ → ℕ → F) (rows lastChunk : ℕ)
    (heq : (∏ c ∈ range (lastChunk + 1), ∏ i ∈ range rows, num c i) =
      ∏ c ∈ range (lastChunk + 1), ∏ i ∈ range rows, den c i) :
    chainedProductRows num den rows lastChunk rows ^ 2 -
      chainedProductRows num den rows lastChunk rows = 0 := by
  change chainedProductInitial num den rows (lastChunk + 1) ^ 2 -
    chainedProductInitial num den rows (lastChunk + 1) = 0
  rw [chainedProductInitial_eq_running]
  exact runningProductRows_terminal_constraint _ _ _ heq

/-- Permuting a row prefix preserves every product of additively shifted values. -/
theorem prefixPerm_prod_shift_eq (a b : ℕ → F) (m : ℕ)
    (hperm : (List.ofFn fun i : Fin m => a i.val).Perm (List.ofFn fun i : Fin m => b i.val))
    (shift : F) : (∏ i ∈ range m, (a i + shift)) = ∏ i ∈ range m, (b i + shift) := by
  have h := (hperm.map (fun x => x + shift)).prod_eq
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def] at h
  rw [Fin.prod_univ_eq_prod_range (fun i => a i + shift) m,
    Fin.prod_univ_eq_prod_range (fun i => b i + shift) m] at h
  exact h

/-- The lookup's exclusive product scan with its two numerator and denominator factors. -/
def lookupProductRows (input table permutedInput permutedTable : ℕ → F) (beta gamma : F) : ℕ → F :=
  runningProductRows
    (fun i => (input i + beta) * (table i + gamma))
    (fun i => (permutedInput i + beta) * (permutedTable i + gamma)) 1

/-- The input and table permutation laws give the lookup's full product identity for all challenges. -/
theorem lookupProductRows_product_identity (input table permutedInput permutedTable : ℕ → F)
    (beta gamma : F) (m : ℕ)
    (hinput : (List.ofFn fun i : Fin m => input i.val).Perm
      (List.ofFn fun i : Fin m => permutedInput i.val))
    (htable : (List.ofFn fun i : Fin m => table i.val).Perm
      (List.ofFn fun i : Fin m => permutedTable i.val)) :
    (∏ i ∈ range m, (input i + beta) * (table i + gamma)) =
      ∏ i ∈ range m, (permutedInput i + beta) * (permutedTable i + gamma) := by
  rw [prod_mul_distrib, prod_mul_distrib,
    prefixPerm_prod_shift_eq input permutedInput m hinput beta,
    prefixPerm_prod_shift_eq table permutedTable m htable gamma]

/-- The computed lookup terminal value satisfies `z²-z`, including zero denominators. -/
theorem lookupProductRows_terminal_constraint (input table permutedInput permutedTable : ℕ → F)
    (beta gamma : F) (m : ℕ)
    (hinput : (List.ofFn fun i : Fin m => input i.val).Perm
      (List.ofFn fun i : Fin m => permutedInput i.val))
    (htable : (List.ofFn fun i : Fin m => table i.val).Perm
      (List.ofFn fun i : Fin m => permutedTable i.val)) :
    lookupProductRows input table permutedInput permutedTable beta gamma m ^ 2 -
      lookupProductRows input table permutedInput permutedTable beta gamma m = 0 :=
  runningProductRows_terminal_constraint _ _ m
    (lookupProductRows_product_identity _ _ _ _ beta gamma m hinput htable)

/-- Nonzero lookup denominator factors give the existing verifier's row recurrence. -/
theorem lookupProductRows_recurrence (input table permutedInput permutedTable : ℕ → F)
    (beta gamma : F) (i : ℕ)
    (hinput : permutedInput i + beta ≠ 0) (htable : permutedTable i + gamma ≠ 0) :
    lookupProductRows input table permutedInput permutedTable beta gamma (i + 1) *
        (permutedInput i + beta) * (permutedTable i + gamma) =
      lookupProductRows input table permutedInput permutedTable beta gamma i *
        (input i + beta) * (table i + gamma) := by
  simpa only [lookupProductRows, mul_assoc] using
    runningProductRows_recurrence
      (fun j => (input j + beta) * (table j + gamma))
      (fun j => (permutedInput j + beta) * (permutedTable j + gamma))
      1 i (mul_ne_zero hinput htable)

end Zcash.Snark.ZeroKnowledge
