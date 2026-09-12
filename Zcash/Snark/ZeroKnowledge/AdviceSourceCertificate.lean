import Zcash.Snark.ZeroKnowledge.AdviceSupportCertificate

/-!
# One source certificate for read and copy checks

Each entry retains the original instruction and its original optional copy tag,
and adds a semantic read certificate. Source transport changes only the erasure
proof, so both finite scans can evaluate the retained data without traversing an
equality cast. Copy semantics and successful scans remain explicit obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Read annotations indexed by the exact original instructions and copy tags. -/
structure AdviceSourceCertificate {F : Type} [FiniteField F]
    (source : List (PlacedAdviceProgram F × Option AdviceAddress)) where
  annotations : List (SupportedAdviceProgram F × Option AdviceAddress)
  erases : annotations.map (fun entry => (entry.1.instruction, entry.2)) = source

/-- The empty source needs no read certificate. -/
def AdviceSourceCertificate.nil {F : Type} [FiniteField F] :
    AdviceSourceCertificate (F := F) [] := ⟨[], rfl⟩

/-- Attach one original tagged instruction with its semantic read proof. -/
def AdviceSourceCertificate.cons {F : Type} [FiniteField F]
    (entry : PlacedAdviceProgram F × Option AdviceAddress) (reads : List (AssignedCell F))
    (support : WitnessFunctionSupport reads (fun env => (entry.1.program.eval env)[0]))
    {rest : List (PlacedAdviceProgram F × Option AdviceAddress)}
    (tail : AdviceSourceCertificate rest) : AdviceSourceCertificate (entry :: rest) where
  annotations := (supportedAdviceProgram entry.1 reads support, entry.2) :: tail.annotations
  erases := by simp only [List.map_cons, supportedAdviceProgram, tail.erases, Prod.mk.eta]

/-- The finite data inspected by the read and alias scans for one original entry. -/
def adviceSourceEntryData {F : Type}
    (entry : PlacedAdviceProgram F × Option AdviceAddress) (reads : List (AssignedCell F)) :
    Column .advice × ℕ × List (AssignedCell F) × Option AdviceAddress :=
  (entry.1.column, entry.1.row, reads, entry.2)

/-- Store proved-equivalent finite data without casting the data through its equality proof. -/
def AdviceSourceCertificate.consWithData {F : Type} [FiniteField F]
    (entry : PlacedAdviceProgram F × Option AdviceAddress) (reads : List (AssignedCell F))
    (support : WitnessFunctionSupport reads (fun env => (entry.1.program.eval env)[0]))
    (data : Column .advice × ℕ × List (AssignedCell F) × Option AdviceAddress)
    (hdata : data = adviceSourceEntryData entry reads)
    {rest : List (PlacedAdviceProgram F × Option AdviceAddress)}
    (tail : AdviceSourceCertificate rest) : AdviceSourceCertificate (entry :: rest) where
  annotations :=
    (({ instruction := ⟨data.1, data.2.1, entry.1.program⟩
        reads := data.2.2.1
        support := by simpa only [hdata, adviceSourceEntryData] using support }, data.2.2.2) ::
      tail.annotations)
  erases := by
    simp only [List.map_cons, hdata, adviceSourceEntryData, tail.erases]

/-- Append original source chunks in their original order. -/
def AdviceSourceCertificate.append {F : Type} [FiniteField F]
    {left right : List (PlacedAdviceProgram F × Option AdviceAddress)}
    (first : AdviceSourceCertificate left) (second : AdviceSourceCertificate right) :
    AdviceSourceCertificate (left ++ right) where
  annotations := first.annotations ++ second.annotations
  erases := by rw [List.map_append, first.erases, second.erases]

/-- Rewrite the source while keeping the scan data definitionally unchanged. -/
def AdviceSourceCertificate.transport {F : Type} [FiniteField F]
    {source target : List (PlacedAdviceProgram F × Option AdviceAddress)}
    (equality : source = target) (certificate : AdviceSourceCertificate source) :
    AdviceSourceCertificate target :=
  ⟨certificate.annotations, certificate.erases.trans equality⟩

/-- Forgetting copy tags yields an exact read certificate for the original programs. -/
def AdviceSourceCertificate.readCertificate {F : Type} [FiniteField F]
    {source : List (PlacedAdviceProgram F × Option AdviceAddress)}
    (certificate : AdviceSourceCertificate source) : AdviceSupportCertificate (source.map Prod.fst) where
  annotations := certificate.annotations.map Prod.fst
  erases := by
    have erased := congrArg (List.map Prod.fst) certificate.erases
    simpa only [List.map_map, Function.comp_def] using erased

/-- The two scans of retained source data imply the original compiler witness equations. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_sourceCertificate
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (source : List (PlacedAdviceProgram Fp × Option AdviceAddress))
    (certificate : AdviceSourceCertificate source)
    (herases : source.map Prod.fst = circuitAdvicePrograms circuit.placement circuit.operations 0)
    (haliasCheck : adviceAliasMapPlan ∅ (adviceAliasAddressData
      (certificate.annotations.map (fun entry => (entry.1.instruction, entry.2)))) = true)
    (hreadCheck : adviceSupportMapPlan circuit.placement ∅ certificate.readCertificate.annotations = true)
    (hsources : AdviceAliasSources circuit.placement source) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  rw [certificate.erases] at haliasCheck
  exact topLevelAdviceAssignment_extendsWitnesses_of_mapPlans circuit initial hints source
    certificate.readCertificate.annotations herases certificate.readCertificate.erases
    haliasCheck hreadCheck hsources

end Zcash.Snark.ZeroKnowledge
