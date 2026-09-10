import Zcash.Snark.ZeroKnowledge.AdviceSupportMapPlan

/-!
# Read annotations indexed by their original source

This certificate keeps the annotated instructions and their exact source-erasure
equation together. Its constructors compose original instructions and source
chunks without changing either their order or their witness programs. A complete
circuit certificate also includes a successful read scan and alias scan.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Read annotations with their checked equality to the complete original program list. -/
structure AdviceSupportCertificate {F : Type} [FiniteField F]
    (source : List (PlacedAdviceProgram F)) where
  annotations : List (SupportedAdviceProgram F)
  erases : annotations.map SupportedAdviceProgram.instruction = source

/-- The empty source has no annotations or obligations. -/
def AdviceSupportCertificate.nil {F : Type} [FiniteField F] :
    AdviceSupportCertificate (F := F) [] := ⟨[], rfl⟩

/-- Attach the actual next instruction using its semantic read certificate. -/
def AdviceSupportCertificate.cons {F : Type} [FiniteField F]
    (instruction : PlacedAdviceProgram F) (reads : List (AssignedCell F))
    (support : WitnessFunctionSupport reads (fun env => (instruction.program.eval env)[0]))
    {rest : List (PlacedAdviceProgram F)} (tail : AdviceSupportCertificate rest) :
    AdviceSupportCertificate (instruction :: rest) where
  annotations := supportedAdviceProgram instruction reads support :: tail.annotations
  erases := by simp only [List.map_cons, supportedAdviceProgram, tail.erases]

/-- Compose source chunks in exactly their original order. -/
def AdviceSupportCertificate.append {F : Type} [FiniteField F]
    {left right : List (PlacedAdviceProgram F)}
    (first : AdviceSupportCertificate left) (second : AdviceSupportCertificate right) :
    AdviceSupportCertificate (left ++ right) where
  annotations := first.annotations ++ second.annotations
  erases := by rw [List.map_append, first.erases, second.erases]

/-- Change the source by a proved equality while retaining definitionally identical annotation data. -/
def AdviceSupportCertificate.transport {F : Type} [FiniteField F]
    {source target : List (PlacedAdviceProgram F)} (equality : source = target)
    (certificate : AdviceSupportCertificate source) : AdviceSupportCertificate target :=
  ⟨certificate.annotations, certificate.erases.trans equality⟩

/-- A source-indexed certificate and the two scans give the original compiler witness equations. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_certificate
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (aliases : List (PlacedAdviceProgram Fp × Option AdviceAddress))
    (certificate : AdviceSupportCertificate (circuitAdvicePrograms circuit.placement circuit.operations 0))
    (haliases : aliases.map Prod.fst = circuitAdvicePrograms circuit.placement circuit.operations 0)
    (haliasCheck : adviceAliasMapPlan ∅ (adviceAliasAddressData aliases) = true)
    (hreadCheck : adviceSupportMapPlan circuit.placement ∅ certificate.annotations = true)
    (hsources : AdviceAliasSources circuit.placement aliases) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  exact topLevelAdviceAssignment_extendsWitnesses_of_mapPlans circuit initial hints aliases
    certificate.annotations haliases (certificate.erases.trans haliases.symm)
    haliasCheck hreadCheck hsources

end Zcash.Snark.ZeroKnowledge
