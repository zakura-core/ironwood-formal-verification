import Zcash.Snark.ZeroKnowledge.PlonkInactiveRows
import Zcash.Snark.ZeroKnowledge.PlonkCopyWitness

/-!
# Changing one inactive usable advice cell

Row 2000 is before suffix masking. Only current, next, and previous advice queries
exist, so changing this row leaves every expression before row 1999 unchanged.
After compiler placement ends, the inactive-selector certificate supplies equality
for arbitrary advice. Original gate and lookup validity therefore survives this
change when placement ends by row 1999.

Copy validity is preserved when the declared copy list does not touch row 2000.
This module keeps the public footprint condition explicit; PlonkUnusedKeygen derives
it for the compiler's typed copy list. These are witness vectors for the reference relation;
the implementation's permitted witness encoding is a separate boundary.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- A usable row with room for both neighboring reads after the Action region placement. -/
def plonkUnusedAdviceRow : Fin 2048 := 2000

/-- This row is retained by the prover's six-row advice mask. -/
theorem plonkUnusedAdviceRow_usable : plonkUnusedAdviceRow.val < 2042 := by decide

/-- Change exactly one Action's advice cell in row 2000 of the supplied witness vector. -/
def plonkUnusedWitness {actions : ℕ} (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (action : Fin actions) (column : Fin 10) (value : Fp) : Fin actions → Fin 10 → Fin 2048 → Fp :=
  fun a c row => if a = action ∧ c = column ∧ row.val = 2000 then value else witness a c row

/-- The selected cell contains the replacement value. -/
theorem plonkUnusedWitness_at {actions : ℕ} (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp) :
    plonkUnusedWitness witness a c value a c plonkUnusedAdviceRow = value := by
  simp [plonkUnusedWitness, plonkUnusedAdviceRow]

/-- Every cell at any other row is unchanged, including other Actions and columns. -/
theorem plonkUnusedWitness_other_row {actions : ℕ} (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp) (b : Fin actions) (d : Fin 10)
    (row : Fin 2048) (hrow : row.val ≠ 2000) :
    plonkUnusedWitness witness a c value b d row = witness b d row := by
  simp [plonkUnusedWitness, hrow]

/-- None of the three supported rotations can read row 2000 from a row before 1999. -/
theorem plonkAdviceRotationRow_ne_unused (rotation : Fin 3) (row : Fin 2048)
    (hrow : row.val < 1999) : (plonkAdviceRotationRow rotation row).val ≠ 2000 := by
  intro heq
  have hlt := row.isLt
  fin_cases rotation <;> simp [plonkAdviceRotationRow, plonkAdviceRotationOffsets] at heq <;> omega

/-- The actual rotated advice feed is unchanged before row 1999. -/
theorem plonkUnusedWitness_advice_before {actions : ℕ}
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp) (b : Fin actions)
    (row : Fin 2048) (hrow : row.val < 1999) (query : ℕ) :
    plonkAdviceRowValues (plonkUnmaskedAdviceRows (plonkUnusedWitness witness a c value)) b row query =
      plonkAdviceRowValues (plonkUnmaskedAdviceRows witness) b row query := by
  by_cases hquery : query < 25
  · simp only [plonkAdviceRowValues, finFn, hquery, ↓reduceDIte, plonkUnmaskedAdviceRows_eval]
    exact plonkUnusedWitness_other_row witness a c value b _ _
      (plonkAdviceRotationRow_ne_unused _ row hrow)
  · simp only [plonkAdviceRowValues, finFn, hquery, ↓reduceDIte]

/-- Every expression has its original value before row 1999, without selector premises. -/
theorem plonkUnusedWitness_expression_before {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp) (b : Fin actions)
    (row : Fin 2048) (hrow : row.val < 1999) (expr : Expr Fp) :
    plonkExpressionRowValue pub (plonkUnmaskedAdviceRows (plonkUnusedWitness witness a c value)) b row expr =
      plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) b row expr := by
  unfold plonkExpressionRowValue
  rw [show plonkAdviceRowValues (plonkUnmaskedAdviceRows (plonkUnusedWitness witness a c value)) b row =
      plonkAdviceRowValues (plonkUnmaskedAdviceRows witness) b row from
    funext (plonkUnusedWitness_advice_before witness a c value b row hrow)]

/-- Compiler placement and an inactive-expression check preserve that expression on the entire domain. -/
theorem plonkKeygenExpressionRowValue_unused {actions : ℕ}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp) (b : Fin actions) (row : Fin 2048) (expr : Expr Fp)
    (hcheck : exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false) expr = true) :
    plonkExpressionRowValue (plonkKeygenPublicPolynomials top instances sigma)
        (plonkUnmaskedAdviceRows (plonkUnusedWitness witness a c value)) b row expr =
      plonkExpressionRowValue (plonkKeygenPublicPolynomials top instances sigma)
        (plonkUnmaskedAdviceRows witness) b row expr := by
  by_cases hrow : row.val < 1999
  · exact plonkUnusedWitness_expression_before _ witness a c value b row hrow expr
  · exact plonkInactiveExpressionRowValue_eq _ _ _ b row expr
      (plonkKeygenPublicPolynomials_inactive_agrees top hk hcolumns hprefix instances sigma row
        (hplacement.trans (Nat.le_of_not_gt hrow))) hcheck

/-- Original gate and lookup validity survives arbitrary replacement of the unused usable cell. -/
theorem plonkOriginalRowsValid_unused {actions k : ℕ} {G : Type*}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 1999)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := k) vk = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (a : Fin actions) (c : Fin 10) (value : Fp) :
    PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma)
      (plonkUnusedWitness witness a c value) := by
  obtain ⟨hgates, hinputs, htables⟩ := plonkInactiveExpressionsCheck_sound (actions := actions) (k := k) vk hcheck
  constructor
  · intro b row expr hexpr
    exact (plonkKeygenExpressionRowValue_unused top hk hcolumns hprefix hplacement instances sigma
      witness a c value b row expr (hgates expr hexpr)).trans (hvalid.gates b row expr hexpr)
  · intro b lookup row
    obtain ⟨target, htarget⟩ := hvalid.lookups b lookup row
    refine ⟨target, ?_⟩
    have hinput := List.map_congr_left (l := vk.lookupInputExprs lookup) (fun expr hexpr =>
      plonkKeygenExpressionRowValue_unused top hk hcolumns hprefix hplacement instances sigma
        witness a c value b (row.castLE (by decide)) expr (hinputs lookup expr hexpr))
    have htable := List.map_congr_left (l := vk.lookupTableExprs lookup) (fun expr hexpr =>
      plonkKeygenExpressionRowValue_unused top hk hcolumns hprefix hplacement instances sigma
        witness a c value b (target.castLE (by decide)) expr (htables lookup expr hexpr))
    exact hinput.trans (htarget.trans htable.symm)

/-- A copy cell at another row sees the same original value and public sigma label. -/
theorem plonkCopyCellPair_unused {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (value : Fp)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (b : Fin actions) (cell : PlonkCopyCell vk.permutationChunks) (hrow : cell.2.1.val ≠ 2000) :
    plonkCopyCellPair pub (plonkUnmaskedAdviceRows (plonkUnusedWitness witness a c value)) b vk.permutationChunks cell =
      plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) b vk.permutationChunks cell := by
  apply congrArg (fun pairs : List (Fp × Fp) => pairs.getD cell.2.2.val (0, 0))
  apply plonkPermutationFactorRows_congr pub _ _ vk.permutationChunks hqueries b cell.1.val cell.2.1.val
  intro column
  exact (plonkUnmaskedAdviceRows_eval (plonkUnusedWitness witness a c value) b column
    (cell.2.1.castLE (by decide))).trans
      ((plonkUnusedWitness_other_row witness a c value b column (cell.2.1.castLE (by decide)) hrow).trans
        (plonkUnmaskedAdviceRows_eval witness b column (cell.2.1.castLE (by decide))).symm)

/-- Original copies remain satisfied when their public footprint avoids the changed row. -/
theorem plonkCopyWitness_unused {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies)
    (havoid : ∀ pair ∈ copies, pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000)
    (a : Fin actions) (c : Fin 10) (value : Fp) :
    PlonkCopyWitness vk pub (plonkUnusedWitness witness a c value) copies := by
  refine ⟨hcopy.unrotated, hcopy.sigma, ?_⟩
  intro b pair hpair
  have hrows := havoid pair hpair
  exact (congrArg Prod.fst
    (plonkCopyCellPair_unused vk pub witness a c value hcopy.unrotated b pair.1 hrows.1)).trans
      ((hcopy.values b pair hpair).trans
        (congrArg Prod.fst
          (plonkCopyCellPair_unused vk pub witness a c value hcopy.unrotated b pair.2 hrows.2)).symm)

end Zcash.Snark.ZeroKnowledge
