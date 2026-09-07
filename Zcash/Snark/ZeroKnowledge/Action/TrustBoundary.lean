import Zcash.Snark.ZeroKnowledge.ActionSimulation
import Zcash.Snark.ZeroKnowledge.ActionCommitments
import Zcash.Snark.ZeroKnowledge.ActionCompilerSimulation
import Zcash.Meta.AxiomCheck

/-!
# The actual Action circuit boundary of the zero-knowledge development

The general selector-padding argument remains in the standard-tier parent census.
Action's public-input layout and compiler data are reached through the existing
opaque circuit package and its proved API. That package carries the named Pallas
point-order dependency. The encoded Vesta comparison additionally carries the
existing Vesta point-order dependency. No new native certificate is introduced.

The four initial selector zeros remain an explicit proposition, not a certificate.
The actual compiler's masking check follows from the proved source classifications
and an explicit selector-routing condition; both captured keys also have their own
kernel-checked predicates.
The actual configure program now supplies the query order and all key dimensions
except the selector-compression count. Given fifteen packed columns, the derived
key supplies the domain, sigma naming, exact copy layout, and complete opening
connection. These facts also instantiate the encoded simulation bound. The
entire compiled degree profile follows from the source and the packer's degree
invariant. Structural source mask certificates survive selector replacement,
query resolution, and verifier-expression translation. The remaining concrete
conditions are the compression count, the routing of nine previous-row selectors
into the four initial zero columns, and those initial values. No native root or
circuit-computation certificate is added.
-/

assert_axioms Zcash.Snark.ZeroKnowledge.ActionInitialSelectorsZero +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionInstanceRows +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionInstanceRows_eq_elements +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionPublicPolynomials +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_instances_eval +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.action_plonkSelectorMaskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_eq_compiler +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionInstanceCommitment_eq_reference +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionSigmaCommitment_eq_reference +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCompilerPublicCommitmentsMatch +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCompilerOpening_eq_public +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_chunkLen_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationSetCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_quotientPieceCount_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_instanceQueryLayout_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_adviceQueryLayout_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_recordedFixedQueries_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_fixedQueryLayout_of_selectorCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationColumns_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_shape_of_fixedQueryCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_referenceShape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionReferencePermutationChunks
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_permutationChunks_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionReferenceKey +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_queryLayout +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_permutationChunks +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_domain +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_sigmaNaming +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copyChunkWidths +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copySigmaIndices +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_copyQueries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_productShape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_publicCommitmentsMatch +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_opening_eq_public +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionCompilerReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorDegrees
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorMaxDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupInputDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupTableDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupInput_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_lookupTable_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupInput_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupTable_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_lookupDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_degreeProfile_of_gates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorDegreeCost
assert_axioms Zcash.Snark.ZeroKnowledge.actionSelectorDegrees_le
assert_axioms Zcash.Snark.ZeroKnowledge.actionSelectorDegreeCost_pos
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_weightedGateDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorReplacement_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_substitutedGate_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierGate_degree_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_gateDegrees +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_degreeProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionPreviousRowSelectors
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceMaskZero
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceMaskSafe
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGateMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupInputMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupTableMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceGateMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupInputMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_sourceLookupTableMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateQueryState_advice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_gateQueryState_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_fixIdx_packedColumn +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_advIdx_initial_retained +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionPreviousSelectorPacking +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionPackedMaskZero
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_packedSelectorBounds +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_substitutedSourceMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_compiledExpressionMaskSafe +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierGate_maskBoundaryCheck +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupInput_maskBoundaryCheck +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupTable_maskBoundaryCheck +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_maskBoundaryCheck +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
