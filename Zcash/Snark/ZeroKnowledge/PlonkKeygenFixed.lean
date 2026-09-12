import Zcash.Snark.ZeroKnowledge.KeygenFixedSupport
import Zcash.Snark.ZeroKnowledge.PlonkPublicRows
import Zcash.Snark.ZeroKnowledge.PlonkMaskBoundary

/-!
# Keygen fixed rows in the reference prover

The fixed polynomials here interpolate the circuit compiler's dense fixed columns.
Only rows 0 and 2041 need explicit boundary values: the structural keygen support
theorem supplies zero at all six masked rows. The remaining finite mask check reads
those two rows from keygen itself, without substituting a captured polynomial.

Instance and sigma rows are supplied inputs. Their circuit/statement and copy-replay
provenance, and the public commitment correspondence, remain separate obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The compiler's fixed columns, restricted to the reference prover's domain. -/
def plonkKeygenFixedRows (top : TopLevelCircuit Fp Config PublicInput) : Fin 29 → Fin 2048 → Fp :=
  fun column row => (top.fixedRows.getD column.val []).getD row.val 0

/-- Public interpolants with the fixed rows supplied by the actual circuit compiler. -/
def plonkKeygenPublicPolynomials {actions : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkPublicPolynomials actions :=
  plonkPublicPolynomialsFromRows instances (plonkKeygenFixedRows top) sigma

/-- The pinned domain size and blinding count give the exact usable-row boundary. -/
theorem plonkKeygen_domainRows (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hblind : top.blindingFactors = 5) :
    top.n = 2048 ∧ top.usableRowsAt top.domainExponent = 2042 := by
  simp only [TopLevelCircuit.n, TopLevelCircuit.usableRowsAt, hk, hblind]
  decide

/-- Key generation makes every fixed column zero in the six-row masking suffix. -/
theorem plonkKeygenFixedRows_zero (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hblind : top.blindingFactors = 5)
    (hcolumns : 29 ≤ top.fixedColumnCount) (column : Fin 29) (row : Fin 2048)
    (hmasked : 2042 ≤ row.val) : plonkKeygenFixedRows top column row = 0 := by
  obtain ⟨hn, hu⟩ := plonkKeygen_domainRows top hk hblind
  exact topLevelFixedRows_zero_of_usable_le top column.val row.val
    (column.isLt.trans_le hcolumns) (by simpa only [hn] using row.isLt)
    (by simpa only [hu] using hmasked)

/-- Read the two usable boundary rows from keygen and use the proved zero suffix. -/
def plonkKeygenMaskBoundaryFixed (top : TopLevelCircuit Fp Config PublicInput)
    (boundary : Fin 8) : ℕ → Fp :=
  if boundary.val < 2 then
    finFn (fun query : Fin 29 => plonkKeygenFixedRows top
      (plonkFixedQueryOrder query) (plonkMaskBoundaryRows boundary))
  else 0

/-- The finite boundary values agree with the public fixed polynomial evaluations. -/
theorem plonkKeygenPublicPolynomials_maskBoundary {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hblind : top.blindingFactors = 5)
    (hcolumns : 29 ≤ top.fixedColumnCount)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (boundary : Fin 8) :
    plonkFixedRowValues (plonkKeygenPublicPolynomials top instances sigma) (plonkMaskBoundaryRows boundary) =
      plonkKeygenMaskBoundaryFixed top boundary := by
  rw [plonkKeygenPublicPolynomials, plonkPublicPolynomialsFromRows_fixedRowValues]
  unfold plonkKeygenMaskBoundaryFixed
  split
  · rfl
  · rename_i hboundary
    have hrow : 2042 ≤ (plonkMaskBoundaryRows boundary).val := by
      fin_cases boundary <;> simp [plonkMaskBoundaryRows] at *
    funext query
    by_cases hquery : query < 29
    · simpa only [finFn, hquery, ↓reduceDIte, Pi.zero_apply] using
        plonkKeygenFixedRows_zero top hk hblind hcolumns
          (plonkFixedQueryOrder ⟨query, hquery⟩) (plonkMaskBoundaryRows boundary) hrow
    · simp [finFn, hquery]

/-- A finite check on the keygen boundary rows supplies the full public mask profile. -/
theorem plonkKeygenPublicPolynomials_maskingProfile {actions k : ℕ} {G : Type*}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hblind : top.blindingFactors = 5)
    (hcolumns : 29 ≤ top.fixedColumnCount)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkMaskBoundaryCheck vk (plonkKeygenMaskBoundaryFixed top) = true) :
    PlonkMaskingProfile vk (plonkKeygenPublicPolynomials top instances sigma) :=
  plonkMaskBoundaryCheck_sound vk _ _
    (plonkKeygenPublicPolynomials_maskBoundary top hk hblind hcolumns instances sigma) hcheck

end Zcash.Snark.ZeroKnowledge
