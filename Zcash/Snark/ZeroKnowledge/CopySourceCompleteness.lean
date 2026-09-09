import Zcash.Snark.ZeroKnowledge.KeygenCopyRows
import Zcash.Snark.ZeroKnowledge.CompiledFixedWitnesses

/-!
# Source completeness of the compiler's ordered copy equations

Ordinary copies retain their declared endpoints. Deferred constants retain the
positional allocation, and the actual fixed environment reads that allocation's
field value. Both streams therefore preserve the original circuit constraints.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Halo2.Layout Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- The nonconstant part of a region's compiled copies is exactly its declared copy projection. -/
theorem regionCopiesSplit_fst_eq_declared (columns : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (constants : List (ℕ × ℕ × ℕ)) :
    (regionCopiesSplit columns starts body constants).1 =
      (regionDeclaredCopies body).filterMap (resolveDeclared columns starts) := by
  change body.filterMap _ = _
  rw [regionDeclaredCopies_eq_filterMap, List.filterMap_filterMap]
  congr 1
  funext operation
  cases operation <;> rfl

/-- The full V1 nonconstant copy stream retains every original declaration in order. -/
theorem v1Copies_fst_eq_declared (columns : List ColRef) (starts : List ℕ)
    (operations : Operations Fp) (constants : List (ℕ × ℕ × ℕ)) :
    (Layout.V1.go columns starts operations constants).1.1 =
      (operationDeclaredCopies operations).filterMap (resolveDeclared columns starts) := by
  induction operations generalizing constants with
  | nil => rfl
  | cons operation rest ih =>
    cases operation with
    | region name body =>
      rcases hsplit : regionCopiesSplit columns starts body constants with ⟨equalities, constantCopies, tail⟩
      rcases hgo : Layout.V1.go columns starts rest tail with ⟨⟨nextEqualities, nextConstants⟩, finalTail⟩
      have hfirst := regionCopiesSplit_fst_eq_declared columns starts body constants
      have hrest := ih tail
      rw [hsplit] at hfirst
      rw [hgo] at hrest
      dsimp only at hrest
      simp only [Layout.V1.go, hsplit, hgo, operationDeclaredCopies, List.filterMap_append,
        hfirst, hrest]
    | constrainInstance cell column row =>
      rcases hgo : Layout.V1.go columns starts rest constants with ⟨⟨nextEqualities, nextConstants⟩, finalTail⟩
      have hrest := ih constants
      rw [hgo] at hrest
      dsimp only at hrest
      simp only [Layout.V1.go, hgo, operationDeclaredCopies, List.filterMap_cons,
        resolveDeclared, hrest]
    | loadTable table values => exact ih constants

/-- Reading a compiler copy endpoint in its ordered permutation-column layout. -/
def sourceCopyValue (columns : List ColRef) (environment : Environment Fp) (cell : ℕ × ℕ) : Fp :=
  environment.get (ColRef.toAny (columns.getD cell.1 (.advice 0))) (cell.2 : ℤ)

/-- Resolving a registered original cell preserves its semantic read. -/
theorem sourceCopyValue_resolveCell (cs : ConstraintSystem Fp) (starts : List ℕ)
    (environment : Environment Fp) (cell : Cell) (hcolumn : cell.column ∈ cs.permutationColumns) :
    sourceCopyValue (Keygen.permColsOf cs) environment (resolveCell (Keygen.permColsOf cs) starts cell) =
      cell.eval (fun region => starts.getD region 0) environment := by
  unfold sourceCopyValue resolveCell
  rw [permCols_getD_permIndex _ _ _ (by rwa [Keygen.permColsOf_map_toAny])]
  rfl

/-- Resolving a registered public-input endpoint preserves its absolute instance read. -/
theorem sourceCopyValue_instance (cs : ConstraintSystem Fp) (environment : Environment Fp)
    (column : Column .instance) (row : ℕ) (hcolumn : column.toAny ∈ cs.permutationColumns) :
    sourceCopyValue (Keygen.permColsOf cs) environment
      (permIndex (Keygen.permColsOf cs) column.toAny, row) = environment.get column.toAny (row : ℤ) := by
  unfold sourceCopyValue
  rw [permCols_getD_permIndex _ _ _ (by rwa [Keygen.permColsOf_map_toAny])]

/-- A resolved nonconstant copy retains the original declared equality. -/
theorem sourceCopyValue_eq_of_resolveDeclared (cs : ConstraintSystem Fp) (starts : List ℕ)
    (environment : Environment Fp) (copy : DeclaredCopy Fp)
    (hleft : copy.1.PermutationColumnRegistered cs) (hright : copy.2.PermutationColumnRegistered cs)
    (hsatisfied : copy.Satisfied (fun region => starts.getD region 0) environment)
    (tuple : ℕ × ℕ × ℕ × ℕ) (hresolve : resolveDeclared (Keygen.permColsOf cs) starts copy = some tuple) :
    sourceCopyValue (Keygen.permColsOf cs) environment (tuple.1, tuple.2.1) =
      sourceCopyValue (Keygen.permColsOf cs) environment (tuple.2.2.1, tuple.2.2.2) := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared] at hresolve
  all_goals try cases hresolve
  case cell.cell left right =>
    rw [sourceCopyValue_resolveCell cs starts environment left hleft,
      sourceCopyValue_resolveCell cs starts environment right hright]
    exact hsatisfied
  case cell.instance left column row =>
    rw [sourceCopyValue_resolveCell cs starts environment left hleft,
      sourceCopyValue_instance cs environment column row hright]
    exact hsatisfied

/-- Original constraints imply all nonconstant equations in the actual compiler copy stream. -/
theorem topLevel_nonconstantCopyValues_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ (Layout.V1.go (Keygen.permColsOf top.constraintSystem) top.regionStarts
      top.operations (Keygen.constantCopyEntries top.constraintSystem top.operations)).1.1) :
    sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.1, tuple.2.1) =
      sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.2.2.1, tuple.2.2.2) := by
  rw [v1Copies_fst_eq_declared] at htuple
  obtain ⟨copy, hcopy, hresolve⟩ := List.mem_filterMap.mp htuple
  have hregistered := operationDeclaredCopies_permutationColumns top.constraintSystem top.operations
    top.keygenCoherent copy hcopy
  have hsatisfied := (CircuitConstraintFamily.copy_constraints_iff_declaredCopies top.placement
    (top.environment assignment) top.operations 0).mp (FullCircuitSatisfaction.of_constraints hconstraints).copies
  exact sourceCopyValue_eq_of_resolveDeclared top.constraintSystem top.regionStarts
    (top.environment assignment) copy hregistered.1 hregistered.2
    (List.forall_iff_forall_mem.mp hsatisfied copy hcopy) tuple hresolve

/-- A region's positional constant site is an original semantic copy declaration. -/
theorem constSite_mem_declaredCopies (body : RegionOperations Fp) (site : Cell × Fp)
    (hsite : site ∈ constSites body) :
    (.cell site.1, .constant site.2) ∈ regionDeclaredCopies body := by
  induction body with
  | nil => simp [constSites] at hsite
  | cons operation rest ih =>
    cases operation <;> simp_all [constSites, regionDeclaredCopies, regionOperationDeclaredCopy?]
    aesop

/-- The whole positional constants stream retains the original declared equality. -/
theorem operationConstSite_mem_declaredCopies (operations : Operations Fp) (site : Cell × Fp)
    (hsite : site ∈ operationConstSites operations) :
    (.cell site.1, .constant site.2) ∈ operationDeclaredCopies operations := by
  induction operations with
  | nil => simp [operationConstSites] at hsite
  | cons operation rest ih =>
    cases operation with
    | region name body =>
      rw [operationConstSites, List.mem_append] at hsite
      rcases hsite with hbody | hrest
      · exact List.mem_append_left _ (constSite_mem_declaredCopies body site hbody)
      · exact List.mem_append_right _ (ih hrest)
    | constrainInstance cell column row => exact List.mem_cons_of_mem _ (ih hsite)
    | loadTable table values => exact ih hsite

/-- Resolving any registered permutation column preserves its absolute environment read. -/
theorem sourceCopyValue_column (cs : ConstraintSystem Fp) (environment : Environment Fp)
    (column : AnyColumn) (row : ℕ) (hcolumn : column ∈ cs.permutationColumns) :
    sourceCopyValue (Keygen.permColsOf cs) environment
      (permIndex (Keygen.permColsOf cs) column, row) = environment.get column (row : ℤ) := by
  unfold sourceCopyValue
  rw [permCols_getD_permIndex _ _ _ (by rwa [Keygen.permColsOf_map_toAny])]

/-- A legacy constant-copy allocation names an actual registered fixed column. -/
theorem topLevel_constantCopyColumn_registered
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (entry : ℕ × ℕ × ℕ)
    (hentry : entry ∈ Keygen.constantCopyEntries top.constraintSystem top.operations) :
    (AnyColumn.mk .fixed entry.2.1) ∈ top.constraintSystem.permutationColumns := by
  rw [Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact top.constantAssignmentColumn_mem_permutationColumns hassignment

/-- The canonical compiler environment reads the exact allocated constant. -/
theorem topLevel_constantCopyValue
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (entry : ℕ × ℕ × ℕ)
    (hentry : entry ∈ Keygen.constantCopyEntries top.constraintSystem top.operations) :
    (top.environment assignment).get ⟨.fixed, entry.2.1⟩ (entry.2.2 : ℤ) = (entry.1 : Fp) := by
  rw [Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  change top.fixedValue ⟨column⟩ (row : ℤ) = (value.val : Fp)
  have hraw : (column, row, value) ∈ Layout.rawAssignments (top.usableRowsAt top.domainExponent)
      top.selectorMap top.constraintSystem top.operations := by
    unfold Layout.rawAssignments
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(value, column, row), hassignment, rfl⟩
  simpa using compiledFixedValue_of_mem_raw top (column, row, value) hraw

/-- Original constraints imply every deferred constant equation emitted by the actual compiler. -/
theorem topLevel_constantCopyValues_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ (Layout.V1.go (Keygen.permColsOf top.constraintSystem) top.regionStarts
      top.operations (Keygen.constantCopyEntries top.constraintSystem top.operations)).1.2) :
    sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.1, tuple.2.1) =
      sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.2.2.1, tuple.2.2.2) := by
  rw [(V1_go_snd_eq (Keygen.permColsOf top.constraintSystem) top.regionStarts top.operations
    (Keygen.constantCopyEntries top.constraintSystem top.operations) (plonkKeygenConstantCopies_fit top)).1]
    at htuple
  obtain ⟨⟨site, entry⟩, hzip, rfl⟩ := List.mem_map.mp htuple
  have hsite := (List.of_mem_zip hzip).1
  have hentry := (List.of_mem_zip hzip).2
  have hsiteColumn := operationConstSite_column_mem_permutationColumns top.constraintSystem
    top.operations top.keygenCoherent hsite
  have hentryColumn := topLevel_constantCopyColumn_registered top entry hentry
  have hentryValue : entry.1 = site.2.val := by
    apply constantAllocation_value top.operations (top.constraintSystem.constants.map (·.index))
    · simpa only [Keygen.constantCopyEntries, List.length_map] using plonkKeygenConstantCopies_fit top
    · exact hzip
  have hsatisfied := (CircuitConstraintFamily.copy_constraints_iff_declaredCopies top.placement
    (top.environment assignment) top.operations 0).mp (FullCircuitSatisfaction.of_constraints hconstraints).copies
  have hsiteValue := List.forall_iff_forall_mem.mp hsatisfied (.cell site.1, .constant site.2)
    (operationConstSite_mem_declaredCopies top.operations site hsite)
  change sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
      (permIndex (Keygen.permColsOf top.constraintSystem) ⟨.fixed, entry.2.1⟩, entry.2.2) =
    sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
      (resolveCell (Keygen.permColsOf top.constraintSystem) top.regionStarts site.1)
  rw [sourceCopyValue_column _ _ _ _ hentryColumn, sourceCopyValue_resolveCell _ _ _ _ hsiteColumn]
  rw [topLevel_constantCopyValue top assignment entry hentry, hentryValue]
  simpa only [ZMod.natCast_zmod_val] using hsiteValue.symm

/-- Original constraints imply every equation in the complete ordered compiler copy list. -/
theorem topLevel_copyValues_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ plonkKeygenCopyRaw top) :
    sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.1, tuple.2.1) =
      sourceCopyValue (Keygen.permColsOf top.constraintSystem) (top.environment assignment)
        (tuple.2.2.1, tuple.2.2.2) := by
  change tuple ∈ (Layout.V1.go (Keygen.permColsOf top.constraintSystem) top.regionStarts
    top.operations (Keygen.constantCopyEntries top.constraintSystem top.operations)).1.1 ++
    (Layout.V1.go (Keygen.permColsOf top.constraintSystem) top.regionStarts
      top.operations (Keygen.constantCopyEntries top.constraintSystem top.operations)).1.2 at htuple
  rcases List.mem_append.mp htuple with hordinary | hconstant
  · exact topLevel_nonconstantCopyValues_of_constraints top assignment hconstraints tuple hordinary
  · exact topLevel_constantCopyValues_of_constraints top assignment hconstraints tuple hconstant

end Zcash.Snark.ZeroKnowledge
