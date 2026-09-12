import Zcash.Snark.ZeroKnowledge.PlonkExpressionRows
import Zcash.Snark.ZeroKnowledge.DomainDivisibility

/-!
# Gate and lookup preservation from original satisfying advice

The witness premises concern its original, unmasked rows: gates vanish and each
lookup input tuple occurs in the corresponding usable table. A separate public
profile certifies that the concrete expressions ignore the cells replaced by masks.
These two inputs imply actual masked gate division and compressed lookup membership
for every challenge record and tape. No successful-construction premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Public expression checks covering gates on the full domain and lookups on usable rows. -/
structure PlonkMaskingProfile {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions) : Prop where
  gates : ∀ row : Fin 2048, ∀ expr ∈ vk.gates,
    plonkExpressionMaskCheck pub row expr = true
  lookupInputs : ∀ lookup : Fin 3, ∀ row : Fin 2042,
    ∀ expr ∈ vk.lookupInputExprs lookup,
      plonkExpressionMaskCheck pub (row.castLE (by decide)) expr = true
  lookupTables : ∀ lookup : Fin 3, ∀ row : Fin 2042,
    ∀ expr ∈ vk.lookupTableExprs lookup,
      plonkExpressionMaskCheck pub (row.castLE (by decide)) expr = true

/-- The supplied original advice satisfies gates and uncompressed lookup tuple membership. -/
structure PlonkOriginalRowsValid {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) : Prop where
  gates : ∀ a : Fin actions, ∀ row : Fin 2048, ∀ expr ∈ vk.gates,
    plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) a row expr = 0
  lookups : ∀ a : Fin actions, ∀ lookup : Fin 3, ∀ row : Fin 2042, ∃ target : Fin 2042,
    (vk.lookupInputExprs lookup).map
        (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) a (row.castLE (by decide))) =
      (vk.lookupTableExprs lookup).map
        (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) a (target.castLE (by decide)))

/-- Public mask safety and original gate validity give division of every actual masked gate. -/
theorem plonkTotalColumnRows_gateConstraints_dvd {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (ch : Challenges k Fp) (tape : Fin (126 * actions) → Fp) (a : Fin actions) :
    ∀ poly ∈ (plonkConstraintModel vk pub ch (plonkTotalColumnRows vk pub witness ch tape)).gateConstraints a,
      (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ poly := by
  intro poly hpoly
  obtain ⟨mapped, hmapped, rfl⟩ := List.mem_map.mp hpoly
  obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp hmapped
  apply domainPolynomial_dvd_of_rows (omegaOf 11) (by decide) (omegaOf_primitiveRoot 11 (by decide))
  intro row
  exact (plonkGatePolynomial_eval_row vk pub ch _ a expr row).trans
    ((plonkExpressionRowValue_masked vk pub witness ch tape a row expr (profile.gates row expr hexpr)).trans
      (hvalid.gates a row expr hexpr))

/-- Lookup tuples still agree after masking, with the same original table-row witness. -/
theorem plonkTotalColumnRows_lookupTuples {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (ch : Challenges k Fp) (tape : Fin (126 * actions) → Fp) (a : Fin actions)
    (lookup : Fin 3) (row : Fin 2042) :
    ∃ target : Fin 2042,
      (vk.lookupInputExprs lookup).map
          (plonkExpressionRowValue pub (plonkTotalColumnRows vk pub witness ch tape) a (row.castLE (by decide))) =
        (vk.lookupTableExprs lookup).map
          (plonkExpressionRowValue pub (plonkTotalColumnRows vk pub witness ch tape) a (target.castLE (by decide))) := by
  obtain ⟨target, htarget⟩ := hvalid.lookups a lookup row
  refine ⟨target, ?_⟩
  have hinput := List.map_congr_left (l := vk.lookupInputExprs lookup) (fun expr hexpr =>
    plonkExpressionRowValue_masked vk pub witness ch tape a _ expr (profile.lookupInputs lookup row expr hexpr))
  have htable := List.map_congr_left (l := vk.lookupTableExprs lookup) (fun expr hexpr =>
    plonkExpressionRowValue_masked vk pub witness ch tape a _ expr (profile.lookupTables lookup target expr hexpr))
  exact hinput.trans (htarget.trans htable.symm)

/-- Original tuple membership supplies actual compressed membership for every compression challenge. -/
theorem plonkTotalColumnRows_lookupMembership {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (profile : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
    (ch : Challenges k Fp) (tape : Fin (126 * actions) → Fp) (a : Fin actions) (lookup : Fin 3) :
    ∀ i < 2042, ∃ j, j < 2042 ∧
      plonkLookupCompressedRows pub (plonkTotalColumnRows vk pub witness ch tape) ch.theta a (vk.lookupInputExprs lookup) i =
        plonkLookupCompressedRows pub (plonkTotalColumnRows vk pub witness ch tape) ch.theta a (vk.lookupTableExprs lookup) j := by
  intro i hi
  obtain ⟨target, htarget⟩ := plonkTotalColumnRows_lookupTuples vk pub witness profile hvalid ch tape a lookup ⟨i, hi⟩
  refine ⟨target.val, target.isLt, ?_⟩
  exact (plonkLookupCompressedRows_eq_values pub _ ch.theta a (vk.lookupInputExprs lookup)
    ((⟨i, hi⟩ : Fin 2042).castLE (by decide))).trans
      ((congrArg (fun values : List Fp => values.foldl (fun acc value => acc * ch.theta + value) 0) htarget).trans
        (plonkLookupCompressedRows_eq_values pub _ ch.theta a (vk.lookupTableExprs lookup)
          (target.castLE (by decide))).symm)

end Zcash.Snark.ZeroKnowledge
