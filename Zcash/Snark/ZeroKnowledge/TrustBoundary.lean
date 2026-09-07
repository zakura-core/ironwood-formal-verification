import Zcash.Snark.ZeroKnowledge.Sampling
import Zcash.Snark.ZeroKnowledge.MaskPolynomials
import Zcash.Snark.ZeroKnowledge.MaskSampling
import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaAttempt
import Zcash.Snark.ZeroKnowledge.IpaRetry
import Zcash.Snark.ZeroKnowledge.IpaSimulator
import Zcash.Snark.ZeroKnowledge.IpaVerifier
import Zcash.Snark.ZeroKnowledge.LinearMaskTranscript
import Zcash.Snark.ZeroKnowledge.RowMaskTranscript
import Zcash.Snark.ZeroKnowledge.PlonkTranscript
import Zcash.Snark.ZeroKnowledge.PlonkMultiopen
import Zcash.Snark.ZeroKnowledge.PlonkSampling
import Zcash.Snark.ZeroKnowledge.PlonkSimulator
import Zcash.Snark.ZeroKnowledge.PlonkQuotientSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCapacitySimulation
import Zcash.Snark.ZeroKnowledge.PlonkDegreeCertificate
import Zcash.Snark.ZeroKnowledge.PlonkRowSimulation
import Zcash.Snark.ZeroKnowledge.PlonkConsistency
import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkFreshBounds
import Zcash.Snark.ZeroKnowledge.RunningProductRows
import Zcash.Snark.ZeroKnowledge.ProductDenominators
import Zcash.Snark.ZeroKnowledge.PlonkLookupRows
import Zcash.Snark.ZeroKnowledge.PlonkPermutationRows
import Zcash.Snark.ZeroKnowledge.LookupSortRows
import Zcash.Snark.ZeroKnowledge.LookupSortExamples
import Zcash.Snark.ZeroKnowledge.PlonkConstruction
import Zcash.Snark.ZeroKnowledge.PlonkConstructedConstraints
import Zcash.Snark.ZeroKnowledge.PlonkProductBounds
import Zcash.Snark.ZeroKnowledge.PlonkProductCertificate
import Zcash.Snark.ZeroKnowledge.PlonkConstructedSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCopySimulation
import Zcash.Snark.ZeroKnowledge.PlonkCopyCertificate
import Zcash.Snark.ZeroKnowledge.PlonkOriginalSimulation
import Zcash.Snark.ZeroKnowledge.PlonkMaskCertificate
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSimulation
import Zcash.Snark.ZeroKnowledge.PlonkSelectorSimulation
import Zcash.Snark.ZeroKnowledge.Observation
import Zcash.Snark.ZeroKnowledge.PlonkDisclosure
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the zero-knowledge development

These pins bound the transitive proof dependencies to Lean's standard axioms. No native-code
axiom or admitted lemma is permitted. Probability distributions are intentionally noncomputable;
the finite sampling program and its declared tape sizes are checked as computable definitions.
`+choice` permits classical choice only in erased proof fields of a plain computable definition;
the checker still rejects noncomputable algorithmic content. No `+native` exemption is used.

The pinned results establish the field-sampling law, both masking constructions, joint
simulation of the IPA stage with supplied or fresh interactive challenges, and joint hiding
of masked columns. The interactive IPA comparison retains errors and emitted prefixes under
supplied codecs; an identity-rejecting codec also gives a checked successful-attempt law and
independent-retry limit. The pre-IPA comparison retains the joint column dependencies, exact
opening groups and emitted scalar order, with supplied challenges and total private constructors.
The computed multi-opening polynomial and folded blind supply a valid IPA input. The joint
pre-IPA/IPA simulation reconstructs that input from the enriched public view, given a public
quotient-evaluation function that agrees with the actual quotient on every reachable row state.
The full batched prover tape is connected to this joint law, and the joint simulator has a
field-coin implementation. The verifier-typed construction computes the constraint numerator
and quotient pieces, and derives quotient agreement using the existing verifier's constraint
function. A public circuit-degree profile now supplies the numerator capacity, with
kernel-checked certificates for the one- and two-Action captured keys. Row-wise constraint
satisfaction supplies exact quotient divisibility. The newer consistency bound retains
the ideal probability of row states that fail division as an explicit error term, so it
does not assume correctness on every random state. The fresh-challenge comparison retains
the entire verifier tape, adding its exceptional-challenge probability and the average
invalid-row probability to the prover's sampling bias. With independent wide-reduced
verifier coins, the challenge term is bounded by `4113/p + 22 × bias`. The later
original-row theorem bounds the remaining row contribution using explicit witness
and public-key conditions. Connecting those conditions to full Action keygen and
integrating the full verifier's grouping remain open.
The product-row scan now has checked recurrence and terminal-value lemmas that retain
zero-denominator cases. Separate factor-family bounds permit a random private prefix
independent of the two product challenges. The actual reference factor lists and their
pre-product challenge independence now apply that bound to the computed denominators;
their contribution to the joint invalid-row event is derived under the complete
independent challenge law.
The computed lookup scan now supplies all five of the existing row constraints from
the compression, permutation, and run-structure facts outside zero denominators.
The actual polynomial selectors and rotations carry this result to domain division.
The specified canonical sorter now supplies the permutation and run-structure facts,
and succeeds for equal-length prefixes whenever each input value occurs in the table.
Its field-specific adapter feeds those facts directly to the existing lookup constraints.
The concrete retained-row constructor now evaluates lookup expressions and packed
permutation factors through the existing polynomial query layout, then calls those
sorts and scans. Its partial schedule preserves sorting failures and the private
prefix. Completed attempts agree on the same tape with the total constructor used
by the joint simulation, and every constructed column retains its computed usable
rows with the actual preceding masked history. Lookup construction uses only theta;
all row construction uses only theta, beta, and gamma. The phase bounds now identify
every construction-time read with the final column state, including rotated queries.
Completed attempts supply one common lookup-sort result and every product scan through
the terminal row. These computed rows give all fifteen lookup and seven permutation
constraint polynomials per Action, outside zero denominator factors and given the packed
copy-product identity. Gate correctness then gives domain division for every constraint
and for the actual numerator. The retained-row correspondence also covers produced
columns in failed prefixes, without conditioning a probability law on success.
The first sixteen columns per Action are pointwise independent of beta, gamma, and
later challenges on a fixed tape. Every actual product denominator factor occurs in
the computed lists. With fifteen packed key references, fresh independent wide-reduced
product coins give a zero-denominator bound of `42882m/p + 2 × bias`, also under any
independent prior private-state law. Both captured keys have kernel-checked three-chunk,
fifteen-reference certificates. Completed partial attempts inherit the event
bound without conditioning on success. The fixed-size uniform row tape realizes the
sequential law already used by the joint simulation.
Exact reordering of independent challenge draws separates beta and gamma from the
other wide-reduced coins without charging the whole verifier tape's bias again.
The averaged invalid-row event is exactly the computed row-tape experiment; it is
covered by failed construction, gate or copy-product prerequisites, and zero
denominators. The resulting concrete joint comparison has error at most
`prerequisiteFailureMass + (42882m + 4113)/p + (148m + 70) × bias`.
Usable advice rows are preserved on every total-construction tape. Both captured
permutation layouts use only unrotated advice queries, so their computed usable factors
equal the original witness factors. Original copy equations propagate through the
replayed copy permutation; public sigma coherence then gives the exact packed product
identity for every challenge and tape. Under these explicit witness and key premises,
the prerequisite mass equals `gateConstructionFailureMass`, and the joint bound carries
only that remaining row error. A public expression checker now proves invariance under
changes to unretained advice, including products killed by fixed zero selectors.
The exact modular rotation rules identify every retained query. Original gate validity
and lookup tuple membership then give masked gate division and compressed lookup
membership on every tape. The successful sorts make the actual partial column runner
complete on that same tape, so `gateConstructionFailureMass` is zero. The resulting
joint reference bound is `(42882m + 4113)/p + (148m + 70) × bias`, given those original
witness conditions and the public masking/copy profiles. All interior rows pass the
mask check automatically; both captured keys have kernel certificates for the eight
remaining boundary rows with the stated captured fixed-query values. Matching those
values to the supplied public polynomials, and connecting the usable-cell copy list
and sigma labels to full Action keygen, remain explicit obligations. The
public-row constructor now supplies all public polynomial degree bounds. For fixed
rows produced by the circuit compiler, a structural proof derives zero throughout
the masked suffix from the bounds on table, constant, selector, and region writes.
This connects six boundary rows to actual keygen and leaves a finite mask check that
reads only rows 0 and 2041 from the compiler. The keygen reference endpoint uses these
constructed polynomials. The selector-only certificates further leave all fourteen
original fixed columns unknown, and a compiler support theorem makes packed selectors
zero from the V1 placement endpoint onward. Given the public column/placement bounds,
only four initial packed-selector zeros remain to be established for the Action circuit.
Relating the supplied instance/sigma rows and public commitments to the deployed key
also remains open. The
sampling comparison alone is not a simulator for failed attempts. The proof string's
terminal rotations use the kernel root certificate.
The complete typed reference proof now exposes each usable advice cell at its domain
challenge on every private tape. The exact mass of this joint challenge/scalar event
separates the full reference laws of row vectors with different usable cells. Under
wide-reduced challenges the lower bound is positive. A common exact simulator for
those two laws is impossible, but an implementation impossibility claim still needs
two permitted satisfying witnesses for the same public statement and execution
correspondence that accounts for errors, retries, and codecs.
These results do not establish a whole-prover simulator, Fiat–Shamir zero-knowledge, or a
Rust-to-Lean refinement.
-/

assert_computable Zcash.Snark.ZeroKnowledge.fieldSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.wordSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.sampleFieldsWith
assert_computable Zcash.Snark.ZeroKnowledge.splitTapeEquiv +choice

assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.idealFieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_apply
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_weightedBias
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_bias_le
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_remainder_pos
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_zero_gt_light
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_ideal
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_one
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_two
assert_axioms Zcash.Snark.ZeroKnowledge.weightedBias_symm
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_map
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_const
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_coordinate
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledAttempt_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_map
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_le_one
assert_axioms Zcash.Snark.ZeroKnowledge.mixedLaws_error_bound

-- Common #225: derive the sparse polynomial and the full scalar from the recursive fold.
assert_computable Zcash.Snark.ZeroKnowledge.coefficientFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.foldByRounds +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaCoefficients +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedIpaScalar +choice
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_coefficientFold
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_powerIndex
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.coeffsToPoly_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial_eval_root
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientEvaluation_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq_zero_of_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.affineLinearForm_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_simulates
assert_axioms Zcash.Snark.ZeroKnowledge.actualSparseIpaScalar_error_bound

-- Common #267: retain the already disclosed evaluation and the unit-weight contribution.
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPair
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskView
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPolynomial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPolynomial_evaluations
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPair_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskView_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_unit_weight
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_at_zero
assert_axioms Zcash.Snark.ZeroKnowledge.actualLinearMaskView_error_bound

-- Joint Common #267 projection: R, r(x), the Q' commitment, and the later group evaluation.
assert_computable Zcash.Snark.ZeroKnowledge.blindedCommitments
assert_computable Zcash.Snark.ZeroKnowledge.LinearMaskTranscript.ofParts
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskCommitmentCores
assert_computable Zcash.Snark.ZeroKnowledge.honestLinearMaskTranscript
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskTranscriptFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskSimulatorFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.blindedCommitments_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.commitmentView_eq
assert_axioms Zcash.Snark.ZeroKnowledge.idealLinearMask_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskTapeEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeLinearMask_eq_idealProver
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskSimulatorFromTape_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledLinearMask_simulation_error_bound

-- The joint IPA view includes the actual cross terms and the aggregate blind, not just `c`.
assert_computable Zcash.Snark.ZeroKnowledge.publicFold
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTerms +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaCoreMessages +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMessageSum +choice
assert_computable Zcash.Snark.ZeroKnowledge.blindIpaMessages
assert_computable Zcash.Snark.ZeroKnowledge.ipaFinalBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskedVector +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.completeIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.chooseIpaScalar +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.ipaTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTerms_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessages_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_blind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskedVector_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.completeIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.IpaTranscript.eq_complete_of_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.ipaBlindsEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_fixed_mask
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpa_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.blinding_bijective_of_card_eq
assert_axioms Zcash.Snark.ZeroKnowledge.chooseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaSimulatorFromFieldCoins_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eleven
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_alphas
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_maskBlind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_roundBlinds
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeIpa_eq_idealProver
assert_axioms Zcash.Snark.ZeroKnowledge.sampledIpaProver_ideal_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledIpa_simulation_error_bound

-- Fresh interactive challenges, including zero challenges and partial output on errors.
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublic.withChallenges
assert_computable Zcash.Snark.ZeroKnowledge.ipaNonzeroChallengeIndex
assert_computable Zcash.Snark.ZeroKnowledge.observeIpaRounds +choice
assert_computable Zcash.Snark.ZeroKnowledge.observeIpaAttempt +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaAttemptObservation +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.uniformIpaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshIpa_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaAttempt_mask_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_right_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_zero_challenge
assert_axioms Zcash.Snark.ZeroKnowledge.observedIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideObservedIpa_simulation_error_bound

-- Success normalization is derived from the actual observer's failures and retry semantics.
assert_computable Zcash.Snark.ZeroKnowledge.ipaPointFamily
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.pointFamily
assert_computable Zcash.Snark.ZeroKnowledge.ipaPointBlindsIndex
assert_computable Zcash.Snark.ZeroKnowledge.ipaSuccessSet +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaTranscriptEquiv
assert_axioms Zcash.Snark.ZeroKnowledge.conditioning_mass_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_event_mass
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_event_mul_mass
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_eventBias
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_common_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.event_mass_add_compl
assert_axioms Zcash.Snark.ZeroKnowledge.success_mass_lower_bound
assert_axioms Zcash.Snark.ZeroKnowledge.retryStep_event_mass
assert_axioms Zcash.Snark.ZeroKnowledge.conditioned_retry_fixedpoint
assert_axioms Zcash.Snark.ZeroKnowledge.retryStep_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.boundedRetries_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.boundedRetries_exhausted
assert_axioms Zcash.Snark.ZeroKnowledge.failure_mass_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.boundedRetries_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.exists_success_of_failure_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaPoints_fixed_mask
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaPoints_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaPoint_identity_mass
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaRounds_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.observeIpaAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSuccess_iff
assert_axioms Zcash.Snark.ZeroKnowledge.uniformIpaRounds_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaRounds_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshIdealIpa_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshIpa_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.ipaRetryFailureBound_eleven_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.successfulIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpa_retry_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpa_eleven_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.IpaPublic.exists_opening
assert_axioms Zcash.Snark.ZeroKnowledge.wideIpaSimulator_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.wideSuccessfulIpa_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.encodedIpa_retries_tendsto

-- The simulated raw equation is the existing verifier's final IPA assembly.
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublic.ofMsm +choice
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.ofProofString
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_eq_foldAll
assert_axioms Zcash.Snark.ZeroKnowledge.computeS_gterm_publicFold
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_evalVector
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_eq_roundSum
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_verifier_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_assembleFinalMsm

-- Joint replacement-row rank, with the real domain constant certified without native axioms.
assert_axioms Zcash.Snark.ZeroKnowledge.rootOfUnityFp_primitiveRoot
assert_axioms Zcash.Snark.ZeroKnowledge.omegaOf_primitiveRoot
assert_axioms Zcash.Snark.ZeroKnowledge.omegaOf_rows_injective
assert_computable Zcash.Snark.ZeroKnowledge.maskedRows
assert_computable Zcash.Snark.ZeroKnowledge.maskedRowPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.advicePolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskRowsLinearMap +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowMaskIndexEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowMaskTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.rowEvaluationsFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedColumnCommitmentCore +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedColumnFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.surjectiveAddMap_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.surjectiveAffineMap_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.rowMask_interpolationNodes_injective
assert_axioms Zcash.Snark.ZeroKnowledge.rowMask_evaluations_surjective
assert_axioms Zcash.Snark.ZeroKnowledge.rowEvaluationLinearMap_apply
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRows_decompose
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRowPolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.rowMaskTapeEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.sampledRowEvaluations_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.advicePolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.productRowPolynomial_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeEquiv_blind
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeMaskedColumn
assert_axioms Zcash.Snark.ZeroKnowledge.maskedColumn_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledMaskedColumn_error_bound

-- Successive private columns and the source's batched field tape.
assert_computable Zcash.Snark.ZeroKnowledge.columnRowSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.columnRowsFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnRowsFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.observeColumnRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.firstTapeEquiv
assert_computable Zcash.Snark.ZeroKnowledge.columnFullSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.columnCoinEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnMaterialFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchToColumnTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedColumnSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.batchedToColumnTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedPreIpaTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnOrder
assert_computable Zcash.Snark.ZeroKnowledge.PrivateColumnId.firstMasked
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnSteps
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnBatches
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnBatches
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowSampleCount_eq_sum
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_length
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnRows
assert_axioms Zcash.Snark.ZeroKnowledge.idealColumnRows_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledColumnRows_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.columnFullSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_cons_apply
assert_axioms Zcash.Snark.ZeroKnowledge.columnMaterialFromTape_eq
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnMaterial
assert_axioms Zcash.Snark.ZeroKnowledge.columnFullSampleCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.batchToColumnTape_fields
assert_axioms Zcash.Snark.ZeroKnowledge.batchedColumnSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrder_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_row_samples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumns_joint_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkColumns_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnBatches_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_sample_count
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_and_ipa_sample_count

-- Joint pre-IPA hiding, retaining all points and correlations among scalar disclosures.
assert_computable Zcash.Snark.ZeroKnowledge.preIpaSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.preIpaCoinEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPreIpaMaskView +choice
assert_computable Zcash.Snark.ZeroKnowledge.preIpaMaskViewFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.batchedPreIpaViewFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaMaskViewFromTape_factor
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePreIpaMaskView
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaScalarView_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealPreIpaMask_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPreIpaMask_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeBatchedPreIpa
assert_axioms Zcash.Snark.ZeroKnowledge.sampledBatchedPreIpa_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkPreIpa_simulation_error_bound

-- The pinned opening-polynomial groups and actual step-5/step-6 scalar computations.
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservationPoints +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFixedQueryOrder
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceQueryOrder
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupPrefix +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateGroupMembers
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningGroups +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupOffset +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateGroupValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkEvaluationScalars +choice
assert_computable Zcash.Snark.ZeroKnowledge.PlonkPreIpaTranscript.messages
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaProjection +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkPreIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscriptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnView_observe
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFirstGroup_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFirstGroup_linearMaskView
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPrivateGroupValues_observe
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkPreIpaTranscript_projection
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscriptFromTape_factor
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkPreIpaTranscript_simulation

-- Computed multi-opening quotients, polynomial commitments, and the actual incoming IPA blind.
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCoefficients +choice
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCommitment +choice
assert_computable Zcash.Snark.ZeroKnowledge.commitmentHornerFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.values +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.interpolant +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.forVerifier +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenFinalPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenFinalBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.multiopenGroupMsm +choice
assert_computable Zcash.Snark.ZeroKnowledge.computedMultiopenOpening +choice
assert_computable Zcash.Snark.ZeroKnowledge.computedMultiopenIpaPublic +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotientBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPairs +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroup +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroups +choice
assert_axioms Zcash.Snark.ZeroKnowledge.coeffsToPoly_polynomialCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientEvaluation_polynomialCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficients_horner
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_zero
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_horner
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_sum
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCommitment_fold
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.residual_eval
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing_monic
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.vanishing_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.opening_denominator_fold
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_eval
assert_axioms Zcash.Snark.ZeroKnowledge.PolynomialOpeningGroup.quotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial_eval
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenQuotientPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenOpening_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenOpening_value
assert_axioms Zcash.Snark.ZeroKnowledge.multiopenFinalPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.computedMultiopenIpaPublic_validOpening
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_nodup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_away
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPairs_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroup_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPolynomial_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningGroups_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPolynomials_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMultiopenIpa_validOpening
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMultiopenIpa_simulation
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkMultiopenIpa_simulation

-- Actual commitment cores and public reconstruction of the IPA input.
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnIndex
assert_computable Zcash.Snark.ZeroKnowledge.privateColumnAt
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningPointIndices
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialOpeningGroups +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkLinearEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkPieceEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPrimeEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentBlindsFromVector
assert_computable Zcash.Snark.ZeroKnowledge.plonkCommitmentCores +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestPlonkMaskView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCollapsedQuotientPoint +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicCommitmentMembers +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicGroupCommitments +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFirstGroupClaims +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicNodeValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicOpening +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicIpaInput +choice
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnOrder_mem
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnAt_index
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_eq_map
assert_axioms Zcash.Snark.ZeroKnowledge.plonkBlindedOpeningGroups_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_column
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_linear
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_piece
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommitmentPolynomials_quotientPrime
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_points
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_columns
assert_axioms Zcash.Snark.ZeroKnowledge.honestPlonkMaskView_groupValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicCommitmentMembers_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicGroupCommitments_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicNodeValues_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicOpening_honest
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicIpaInput_honest

-- Joint simulation through the actual private state and complete batched field tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkIpaData +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointViewFromTape +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskSimulatorFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointSimulatorFromCoins +choice
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_rows_mem
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_maskView
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_maskView_simulation
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkMaterial
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkJoint
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.uniformColumnViews_ofFn
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaskSimulatorFromFieldCoins_eq
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJointSimulatorFromFieldCoins_program
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJointSimulatorFromFieldCoins_eq

-- The actual constraint calculation, computed quotient, and existing proof-string output.
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofShape
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofString
assert_computable Zcash.Snark.ZeroKnowledge.plonkClaimProof
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofFromJointView +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierHx +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQueryFactors +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkRotatedColumn +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkSelectors +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstraintModel +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator +choice
assert_computable Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlock +choice
assert_computable Zcash.Snark.ZeroKnowledge.domainQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotient +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkQuotientPieces +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkHonestQuotientPieces +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofShape_eleven
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_allExpressions
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierHx_proof
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eq_fold
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_eval_div
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlock_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlocks_recombine
assert_axioms Zcash.Snark.ZeroKnowledge.polynomialCoefficientBlocks_eval
assert_axioms Zcash.Snark.ZeroKnowledge.domainQuotient_natDegree
assert_axioms Zcash.Snark.ZeroKnowledge.domainQuotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPieces_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_natDegree
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotient_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkQuotientPieces_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkHonestQuotient_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_simulation_error_bound

-- Quotient capacity follows from public syntax rather than a private-state degree premise.
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLagrangePolynomials_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.constraintModel_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_natDegree_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_natDegree_lt
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkDegreeProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkDegreeProfile
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_capacity_simulation_error_bound

-- Row-wise constraint satisfaction supplies exact domain division.
assert_axioms Zcash.Snark.ZeroKnowledge.rowDomain_product
assert_axioms Zcash.Snark.ZeroKnowledge.domainPolynomial_dvd_of_rows
assert_axioms Zcash.Snark.ZeroKnowledge.rows_zero_of_domainPolynomial_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.domainPolynomial_dvd_iff_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialFold_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintNumerator_dvd_of_rows
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_rows_simulation_error_bound

-- Private exceptional states contribute their probability to the joint comparison.
assert_axioms Zcash.Snark.ZeroKnowledge.arbitraryMixedLaws_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_rows
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_exceptional_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkJoint_exceptional_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInvalidRowMass_le_row_violation
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_consistency_error_bound

-- The complete public tape is retained; exceptional challenges are charged, not excluded.
assert_axioms Zcash.Snark.ZeroKnowledge.variableMixedLaws_error_bound
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengesFromTape
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_sampling_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifier_simulation_error_bound

-- Concrete exceptional-challenge count for the full interactive tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkRotationExponent
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotationExponent_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_snoc
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservationPoints_away
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengesGood_of_simple
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallenges_bad_cover
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallengeBadEvent_le
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideFreshPlonkVerifier_simulation_error_bound

-- Computed product rows, with zero-preserving division and explicit exceptional factors.
assert_computable Zcash.Snark.ZeroKnowledge.runningProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_zero
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_succ
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_eq_ratio
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_violation_iff
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_zero_after_den_zero
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_end
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_end_one
assert_axioms Zcash.Snark.ZeroKnowledge.runningProductRows_terminal_constraint
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductInitial
assert_computable Zcash.Snark.ZeroKnowledge.chainedProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_start
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_chain
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductInitial_eq_running
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.chainedProductRows_terminal_constraint
assert_axioms Zcash.Snark.ZeroKnowledge.prefixPerm_prod_shift_eq
assert_computable Zcash.Snark.ZeroKnowledge.lookupProductRows
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_product_identity
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_terminal_constraint
assert_axioms Zcash.Snark.ZeroKnowledge.lookupProductRows_recurrence
assert_axioms Zcash.Snark.ZeroKnowledge.uniformProductDenominator_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominator_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominator_mixture_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePinnedProductDenominator_bad_le

-- The computed lookup scan satisfies the actual row and polynomial constraints.
assert_computable Zcash.Snark.ZeroKnowledge.rowSelectorValues
assert_computable Zcash.Snark.ZeroKnowledge.lookupRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.rowSelectorValues_active
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLagrangePolynomials_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSelectors_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_polynomial_eval
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_eval_row_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_dvd_domain_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_lookupEvals
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_lookups

-- The three permutation scans, their actual constraints, and terminal rotations.
assert_axioms Zcash.Snark.ZeroKnowledge.copyPermutation_product_identity
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowNumerator +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowDenominator +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationScanRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationRowEvaluations
assert_axioms Zcash.Snark.ZeroKnowledge.permChunkExpression_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_zero_of_scan
assert_computable Zcash.Snark.ZeroKnowledge.permutationTerminalPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.permutationPairRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_eval_row_zero_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.permutationExpressions_dvd_domain_of_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTerminalFactor
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_permutationSetEvals

-- The specified lookup sorter succeeds on valid prefixes and supplies the row premises.
assert_computable Zcash.Snark.ZeroKnowledge.lookupRunPlan
assert_computable Zcash.Snark.ZeroKnowledge.reserveLookupValues
assert_computable Zcash.Snark.ZeroKnowledge.fillLookupPlan
assert_computable Zcash.Snark.ZeroKnowledge.canonicalLookupSort
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortColumns
assert_computable Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_length
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_perm
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_ordered
assert_axioms Zcash.Snark.ZeroKnowledge.canonicalLookupSort_eq_of_ordered
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_getElem
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_matches
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValues_perm
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlan_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_first
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_run
assert_axioms Zcash.Snark.ZeroKnowledge.ofFn_getD_eq
assert_axioms Zcash.Snark.ZeroKnowledge.reserveLookupValues_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupPlan_reserved_le_length
assert_axioms Zcash.Snark.ZeroKnowledge.fillLookupPlan_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupRunPlan_reservations
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortColumns_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes_exists
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSortedPrefixes_correct
assert_axioms Zcash.Snark.ZeroKnowledge.lookupExpressions_zero_of_sort
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_reverse_fill_example
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_duplicate_table_example
assert_axioms Zcash.Snark.ZeroKnowledge.lookupSort_missing_value_example

-- Partial column construction, exact earlier histories, and the concrete schedule.
assert_computable Zcash.Snark.ZeroKnowledge.ColumnAttemptStep.totalize +choice
assert_computable Zcash.Snark.ZeroKnowledge.columnAttemptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_length_le
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_eq_take
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_eq_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.ColumnAttemptStep.retained
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_retained
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupBaseRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_eq_model
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials_eq_model
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows_exists
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_advice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_eq_none
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_lookup_challenges
assert_computable Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkColumnAttempt +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_totalize
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_row_samples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_eq_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_sampling_error_bound

-- The actual schedule's prefix reads, retained rows, and product constraints.
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnIndex_bounds
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRotatedColumn_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationPairPolynomials_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupSortedRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationBaseRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupBaseRows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.privateColumnPolynomial_eval_row_of_present
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnConstructionSteps_at_index
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_retained_of_present
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_retained
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_advice_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookup_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookup_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_permutation_scan
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_lookupConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_permutation_polynomials
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_permutationConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_domain_division

-- Concrete pre-product causality and zero-denominator probabilities.
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_take_congr
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeColumnRows_cast
assert_computable Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_length
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapePlonkTotalColumnRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_eq_totalRows_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_take_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_take_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_polynomial_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_permutation_factors
assert_axioms Zcash.Snark.ZeroKnowledge.productDenominatorListBad
assert_axioms Zcash.Snark.ZeroKnowledge.productDenominatorListBad_iff
assert_axioms Zcash.Snark.ZeroKnowledge.wideProductDenominatorList_bad_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkProductGammaForms +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductDenominatorsNonzero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_lookup_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_permutation_mem
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductDenominatorsNonzero_of_not_listBad
assert_computable Zcash.Snark.ZeroKnowledge.withProductChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductBetaOffsets_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProductGammaForms_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkProductDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePinnedPlonkProductDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkProductDenominators_mixture_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkColumnAttempt_productDenominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkProductShape
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkProductShape

-- The full challenge law and concrete row exceptions inside the joint simulation.
assert_computable Zcash.Snark.ZeroKnowledge.plonkOtherChallengesFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOtherChallengesFromTape_products
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkOtherChallenges
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_products
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkRowPrerequisites
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_domain_division
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_invalid_cover
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceRowTapeLaw_denominators_bad_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkInvalidRowMass_referenceRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkInvalidRowMass_le_prerequisites
assert_axioms Zcash.Snark.ZeroKnowledge.wideConstructedPlonkVerifier_simulation_error_bound

-- Original copy equations survive masking and supply the computed product identity.
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromCoins_retained
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_retained
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows_polynomial
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnmaskedAdviceRows_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_advice_rows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryOrder_current
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_current
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationRefUnrotated
assert_computable Zcash.Snark.ZeroKnowledge.plonkPermutationQueriesUnrotated
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationRef_usable
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_masked
assert_axioms Zcash.Snark.ZeroKnowledge.copyValues_replay
assert_axioms Zcash.Snark.ZeroKnowledge.prod_chunk_cells
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkCopyCell
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellPair +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellName +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellEntry
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellSigma +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_sigma
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationNumerator_prod_cells
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationDenominator_prod_cells
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkCopyWitness
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyWitness_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_copyProduct
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisites_iff_of_copy
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionFailureMass
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass_eq_of_copy
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopyQueries
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopyQueries
assert_axioms Zcash.Snark.ZeroKnowledge.wideCopyValidPlonkVerifier_simulation_error_bound

-- Original gate and lookup validity, public mask safety, and completion of the actual row attempt.
assert_computable Zcash.Snark.ZeroKnowledge.exprPublicValue
assert_axioms Zcash.Snark.ZeroKnowledge.exprPublicValue_sound
assert_computable Zcash.Snark.ZeroKnowledge.exprMaskInvariant
assert_axioms Zcash.Snark.ZeroKnowledge.exprMaskInvariant_of_retained_all
assert_axioms Zcash.Snark.ZeroKnowledge.exprMaskInvariant_sound
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRotationOffsets
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRotationRow
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceQueryRetained
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryFactor_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_advice_eval_row
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceRowValues +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_adviceRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceRowValues_masked
assert_axioms Zcash.Snark.ZeroKnowledge.columnAttemptFromTape_complete_of_total
assert_axioms Zcash.Snark.ZeroKnowledge.columnRowsFromTape_cast_eq
assert_computable Zcash.Snark.ZeroKnowledge.plonkFixedRowValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkInstanceRowValues +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkExpressionRowValue +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkExpressionMaskCheck +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_fixedRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPolynomialClaimProof_instanceRowValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkExpressionRowValue_masked
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGatePolynomial_eval_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkLookupCompressedRows_eq_values
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkOriginalRowsValid
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_gateConstraints_dvd
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_lookupTuples
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_lookupMembership
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstructColumnResult_ne_none_of_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_of_sorted
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnAttempt_complete_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionReady_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkGateConstructionFailureMass_eq_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisites_of_original
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRowPrerequisiteFailureMass_eq_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wideOriginalValidPlonkVerifier_simulation_error_bound
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows
assert_computable Zcash.Snark.ZeroKnowledge.plonkLookupMaskBoundaryRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows_lookup
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceQueryRetained_interior
assert_axioms Zcash.Snark.ZeroKnowledge.plonkExpressionMaskCheck_interior
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskingProfile_of_boundaries
assert_computable Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryCheck
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryCheck_sound
assert_computable Zcash.Snark.ZeroKnowledge.capturedPlonkMaskBoundaryFixed +choice
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkMaskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkMaskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkMaskingProfile

-- Structural keygen support and public row-polynomial provenance.
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelRawFixed_row_lt_usable
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelFixed_row_lt_usable
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelFixedRows_zero_of_usable_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_instances_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_fixed_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_sigma_eval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_degree
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPublicPolynomialsFromRows_fixedRowValues
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygen_domainRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows_zero
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenMaskBoundaryFixed +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_maskBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_maskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.wideKeygenPlonkVerifier_simulation_error_bound

-- Partial public information and selector placement reduce the concrete mask check to row zero.
assert_computable Zcash.Snark.ZeroKnowledge.exprPartialPublicValue
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialPublicValue_refines
assert_computable Zcash.Snark.ZeroKnowledge.exprPartialMaskInvariant
assert_axioms Zcash.Snark.ZeroKnowledge.exprPartialMaskInvariant_refines
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelRawSelector_row_lt_placementEnd
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorRows_zero_of_placementEnd_le
assert_computable Zcash.Snark.ZeroKnowledge.plonkPartialMaskBoundaryCheck
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPartialMaskBoundaryCheck_sound
assert_computable Zcash.Snark.ZeroKnowledge.plonkInitialMaskColumns
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInitialMaskColumns_bounds
assert_computable Zcash.Snark.ZeroKnowledge.plonkSelectorBoundaryKnown +choice
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkSelectorBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkSelectorBoundary
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFixedQueryOrder_selector
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskBoundaryRows_after_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenFixedRows_selector_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_selectorBoundary_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_selectorMaskingProfile
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkKeygenSelectorProfile
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkKeygenSelectorProfile
assert_axioms Zcash.Snark.ZeroKnowledge.wideSelectorKeygenPlonkVerifier_simulation_error_bound

-- At an unmasked row the disclosed evaluation is the original cell, for every mask law.
assert_axioms Zcash.Snark.ZeroKnowledge.maskedRowPolynomial_eval_before
assert_axioms Zcash.Snark.ZeroKnowledge.advicePolynomial_eval_usable
assert_axioms Zcash.Snark.ZeroKnowledge.evaluationView_apply_at_point
assert_axioms Zcash.Snark.ZeroKnowledge.evaluationView_ne_of_disclosed_cell
assert_axioms Zcash.Snark.ZeroKnowledge.adviceEvaluationView_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.adviceEvaluationView_ne_under_wide_reduction

-- The same disclosure is retained by the complete typed reference proof and challenge tape.
assert_computable Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.projectedKernelView_apply_at_point
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkChallenges_x
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkChallenges_x
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_current
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_usable
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_advice_usable
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifierProver_ne_of_usable_cell
assert_computable Zcash.Snark.ZeroKnowledge.plonkAdviceObservation
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_advice_mass
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_advice_separation
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkVerifierProver_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_advice_separation
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_ne_of_usable_cell
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkVerifierProver_no_common_exact_simulator
