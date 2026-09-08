import Zcash.Snark.ZeroKnowledge.ActionSelectorReplacement
import Zcash.Snark.ZeroKnowledge.ActionTracePlacement
import Zcash.Snark.ZeroKnowledge.ActionSimulation
import Zcash.Snark.ZeroKnowledge.ActionCommitments
import Zcash.Snark.ZeroKnowledge.ActionCompilerSimulation
import Zcash.Snark.ZeroKnowledge.ActionCompilerMasking
import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes
import Zcash.Snark.ZeroKnowledge.ActionCompressionInput
import Zcash.Snark.ZeroKnowledge.ActionOrderedPlacement
import Zcash.Snark.ZeroKnowledge.ActionOrderedSort
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionCompressionCertificate
import Zcash.Snark.ZeroKnowledge.ActionInstantiation
import Zcash.Snark.ZeroKnowledge.ActionPrng
import Zcash.Snark.ZeroKnowledge.ActionRetryLimit
import Zcash.Snark.ZeroKnowledge.ActionDigest
import Zcash.Snark.ZeroKnowledge.ActionFiatShamir
import Zcash.Snark.ZeroKnowledge.ActionFiatShamirBits
import Zcash.Snark.ZeroKnowledge.ActionFiatShamirRetry
import Zcash.Snark.ZeroKnowledge.ActionPrngSecurity
import Zcash.Snark.ZeroKnowledge.ActionGeneratorPrng
import Zcash.Snark.ZeroKnowledge.ActionPrivateRetryBits
import Zcash.Meta.AxiomCheck

/-!
# The actual Action circuit boundary of the zero-knowledge development

The general selector-padding argument remains in the standard-tier parent census.
Action's public-input layout and compiler data are reached through the existing
opaque circuit package and its proved API. That package carries the named Pallas
point-order dependency. The encoded Vesta comparison additionally carries the
existing Vesta point-order dependency. No new native certificate is introduced.

The actual compiler's masking profile follows from the source classifications,
activation trace, evaluated replacement polynomials, and checked compression count.
The older selector-only route still records initial packed-column
zeros and selector routing as premises; the main simulation no longer uses that route.
The actual configure program supplies the query order and all key dimensions.
The exact legacy sort, V1 placement, complete activation fold, and greedy packing
calculation certify fifteen packed columns. The derived
key supplies the domain, sigma naming, exact copy layout, and complete opening
connection. These facts also instantiate the encoded simulation bound. The
entire compiled degree profile follows from the source and the packer's degree
invariant. Structural source mask certificates survive selector replacement,
query resolution, and verifier-expression translation. No native root or
circuit-computation certificate is added.

The complete source trace now proves that all nine previous-row selectors are
inactive at global row zero. The ordered synthesis summary also supplies exactly
the compiler's V1 starts and absolute activation list. These source refinements
also prove that the inactive guards' replacement polynomials vanish after
compression, including at another active selector's nonzero root. These actual
boundary values now supply the main simulation's complete masking profile.
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

assert_axioms Zcash.Snark.ZeroKnowledge.ActionZkRelation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkRelation_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.capturedActionURS +choice
assert_axioms Zcash.Snark.ZeroKnowledge.capturedActionURS_rounds
assert_axioms Zcash.Snark.ZeroKnowledge.capturedActionURS_blinding_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wideCapturedActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_computable Zcash.Snark.ZeroKnowledge.actionZkRunFromRawTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProverFromSource +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProverFromSource_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.sourceActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrngReduction +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.seededActionZk_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZk_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkSimulator_retry_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkProver_retry_lt_one +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkSimulator_retry_lt_one +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetryProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetrySimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkRetryProver_truncate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_expected_attempts_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_length_tail_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideUnlimitedActionZk_simulation_capstone +native(
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

-- Exact source selector traces and their connection to compiler placement.
assert_axioms Zcash.Snark.ZeroKnowledge.witnessPoint_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessNonIdPoint_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeAdd_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaLoad_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.loadPrivate_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthWitness_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.runningSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortRangeCheck_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheck_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckAt_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.rangeCheckAtDecomposed_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.copyCheck_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.incompleteRoundsSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.incompleteSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteRound_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteLoop_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.incomplete_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.completeRoundsSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.completeStartCopy_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.complete_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.variableBaseMainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.variableBaseMain_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.overflowGate_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.overflow_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.variableBaseSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.variableBase_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_trace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.variableBaseMainSelectorTrace_initial
assert_axioms Zcash.Snark.ZeroKnowledge.actionVariableBaseMain_initial_selector +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The complete source trace, composed from all Action subcircuits.
assert_computable Zcash.Snark.ZeroKnowledge.shortSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessShortCheck_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCheck_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessCheckDecomposed_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaRoundsSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaPieceSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaPiece_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaSlot_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaChainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaChain_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaHashSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaHash_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaHash_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.witnessMessagePiece_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.condSwap_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleDecomposition_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.merkleHashSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleHash_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.merkleLayerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleLayer_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.merkleRoot_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.incompleteAdd_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.decomposeEnable_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.decomposeAssign_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.copyDecompose_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedConstantsWindow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedConstantsLoop_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedWindow_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.fixedWindowChainSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fixedWindowChain_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthWindow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthScalar_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.fullWidthInnerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidthInner_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.fullWidth_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.runningFixedInnerSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortInner_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortSign_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.shortFixed_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldInner_regionSelectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldCheck13_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.baseFieldFixed_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonFullRound_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonPartialRound_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.poseidonPermutationSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonPermutation_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonInit_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonInput_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.poseidonHash_selectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.addChip_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.valueCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.valueCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.spendAuthoritySelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.spendAuthority_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.addressIntegritySelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.addressIntegrity_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.nullifierSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.nullifier_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.sinsemillaCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.sinsemillaCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkGate_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkCanonicity_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.commitIvkPiecesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvkPieces_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.commitIvkSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.commitIvk_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeB_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeD_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeE_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeG_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteDecomposeH_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteGdCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePkdCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteValueCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteRhoCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePsiCanonicity_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteYCanonicity_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteYSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteY_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.notePiecesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.notePieces_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteChecksSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteChecks_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.noteGatesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteGates_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.noteCommitSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.noteCommit_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionChecksSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthChecks_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrchardChecks_regionSelectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionNotesSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthNotes_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionBaseSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSynthesizeBase_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBaseCall_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddressRow_regionSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddress_selectorTrace
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceSelectorTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionMainPost_selectorTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorTrace_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_sourceTrace +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Initial source inactivity and exact summary-derived placement.
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceSelectorTrace_initialCheck
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_previousSelector_initial_inactive +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceRegionStarts +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceRegionStarts_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_source +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionSourceSelectorActivations +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionSourceSelectorActivations_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_source +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_previousSelector_replacement_zero +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Actual compiler values discharge masking without initial-column or routing premises.
assert_computable Zcash.Snark.ZeroKnowledge.actionBoundaryFixedKnown +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_selector +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_initial_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionBoundaryQueryKnown_later_fixed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_substitutedPartialMaskCertificates +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_compiledExpressionMaskSafe_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierGate_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupInput_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_verifierLookupTable_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_maskBoundaryCheck_values +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionReferenceKey_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The exact ordered source shapes, with kernel-checked stage certificates.
assert_computable Zcash.Snark.ZeroKnowledge.actionRegionShapeTable
assert_computable Zcash.Snark.ZeroKnowledge.actionWitnessRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionWitnessRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionChecksRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionChecksRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionNotesRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionNotesRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionCrossAddressRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionCrossAddressRegionShapes_eq_source
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_eq_source
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_wellFormed

-- The actual compiler count is the finite calculation on those certified inputs.
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts_def
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_ordered +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_selectorActivations_eq_ordered +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOrderedSelectorCount +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_newFixedCols_eq_orderedCount +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Exact starts for every block in the concrete ordered placement certificate.
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementTrace
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementTrace_lawful
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementShapes
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedPlacementStarts
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementStarts_eq_slot
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedPlacementShapes_length

-- The source's exact legacy-sort order and the corresponding source-indexed starts.
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes
assert_computable Zcash.Snark.ZeroKnowledge.actionSortedRegionIndices
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionShapes_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_indices
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_length
assert_computable Zcash.Snark.ZeroKnowledge.actionRegionStartsCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionSortedRegionShapes_summaries
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedRegionStarts_eq_certificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_regionStarts_eq_certificate +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The complete activation table and the closed fifteen-column compiler count.
assert_computable Zcash.Snark.ZeroKnowledge.actionSelectorBitsCertificate
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations_length
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorActivations_bits
assert_axioms Zcash.Snark.ZeroKnowledge.actionOrderedSelectorCount_eq_fifteen
assert_axioms Zcash.Snark.ZeroKnowledge.actionCircuit_newFixedCols_eq_fifteen +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The same Action comparison before encoding and with exact raw hash responses.
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionCompilerTypedReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkTyped_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver_encoded +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedSimulator_encoded +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkTypedProver_digest_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionZkDigest_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Single-attempt classical oracle simulation, executable tapes, and resource bounds.
-- ActionFiatShamir
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_challengeSchedule +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_prover_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_program_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamir_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleAdversary
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleRequest
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleSelection +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleAdversary +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOraclePreprocessing +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOraclePreprocessing_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOraclePublicContext +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleAdversary_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleConflicts
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRawOracleView_failure_anchor
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_firstAdvice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_programming_failure_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_cached_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleModel
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleInitial +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.ActionOracleTape
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleTapeLaw
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleDigestView +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleDigestView_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleComp +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleComp_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRunTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRunTape_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleProgramView +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRunTape_eq_programmed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracle_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleResources
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRealExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleSimulator
assert_axioms Zcash.Snark.ZeroKnowledge.actionZkDigestSimulator_raw_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorProgram +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorProgram_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulator_field_queryBound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Fixed uniform bit tapes and the complete oracle simulator reduction budget.
-- ActionFiatShamirBits
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirBits_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirBits_binary_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleBits
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorBitCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorBitCount_eleven
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBit_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromTapes_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleWide
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorWordCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorWordCount_eleven
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromRawTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator_program +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWideSimulator_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleWide_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Finite retained retries with shared oracle state and exact tape laws.
-- ActionFiatShamirRetry
assert_axioms Zcash.Snark.ZeroKnowledge.ActionOracleRetryAdversary +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPreprocessing +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPreprocessing_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryContinuation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirRetry_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionFiatShamirRetry_binary_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryRealExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySimulatedExperiment_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetry
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleBitRetriesFromTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_fromTape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_fromTape +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetryResources
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleProver_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleSimulatorFromBits_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitSimulator_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_cache_length_le +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetries_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_keeps +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleBitRetries_tape_bits

-- Uniform-seed PRNG game and exact test-dependent reduction.
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrngSecurity_game_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedActionZk_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- Continuous generator state, exact private-prefix replay, and the finite PRNG reduction.
-- ActionOracleRetrySource
assert_computable Zcash.Snark.ZeroKnowledge.RawPrivateRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.OracleReplyRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.actionRawOracleTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.actionRawOracleTape_law
assert_computable Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromRawTapes +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromSource +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetriesFromSource_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionGeneratorRetry
assert_computable Zcash.Snark.ZeroKnowledge.actionGeneratorRetryTape
assert_computable Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_replay +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_state +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratorRetryTape_at
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_source_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetries_word_budget +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionOracleRetryPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceContinuation +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetrySourceExperiment_uniform +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPrngReduction +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionOracleRetryPrng_game_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.uniformSeedActionFiatShamirRetry_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionGeneratorPrng
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryExperiment +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionGeneratedOracleRetryExperiment_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.generatedActionFiatShamirRetry_test_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- ActionPrivateRetryBits
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitCount
assert_axioms Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitCount_eq
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryRawEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.actionPrivateRetryBitsEquiv +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformActionPrivateRetryBits
