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
import Zcash.Snark.ZeroKnowledge.PlonkUnusedCertificate
import Zcash.Snark.ZeroKnowledge.PlonkUnusedKeygen
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSimulation
import Zcash.Snark.ZeroKnowledge.PlonkAttemptSimulation
import Zcash.Snark.ZeroKnowledge.PlonkFailures
import Zcash.Snark.ZeroKnowledge.PlonkCompilerSuccess
import Zcash.Snark.ZeroKnowledge.PlonkCompilerRetry
import Zcash.Snark.ZeroKnowledge.PlonkCausality
import Zcash.Snark.ZeroKnowledge.IpaCausality
import Zcash.Snark.ZeroKnowledge.PlonkSigmaCertificate
import Zcash.Snark.ZeroKnowledge.BlindingGenerator
import Zcash.Snark.ZeroKnowledge.PlonkEncoding
import Zcash.Snark.ZeroKnowledge.PlonkBinaryBounds
import Zcash.Snark.ZeroKnowledge.PlonkCommitmentRouting
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the zero-knowledge development

These pins bound the transitive proof dependencies to Lean's standard axioms. No native-code
axiom or admitted lemma is permitted. Probability distributions are intentionally noncomputable;
the finite sampling program and its declared tape sizes are checked as computable definitions.
`+choice` permits classical choice only in erased proof fields of a plain computable definition;
the checker still rejects noncomputable algorithmic content. No `+native` exemption is used
in this census. `Vesta/TrustBoundary` and `Action/TrustBoundary` separately name the
existing curve-order dependencies of those concrete specializations.

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
values to the supplied public polynomials and connecting witness values and public
commitments to full Action keygen remain explicit obligations. The ordered compiler
copy-list and sigma-row adapters are checked below. The
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
those two laws is impossible. The inactive-expression certificates for both captured
keys now allow a second valid reference witness to be constructed from any first one:
add one to an advice cell in row 2000, assuming placement ends by row 1999 and copies
avoid the changed row. The gate, lookup, and copy relation is preserved for the same
public statement. The compiler refinement now computes the complete ordered V1 copy list,
including deferred constants, and packs its endpoint coordinates into the prover's cell
type. Re-encoding is the identity on the source list. With fifteen permutation columns,
the checked seven/seven/one widths, and an operation footprint ending by row 1999, the
compiler supplies both placement and the unused-row copy condition. The later sigma
refinement embeds usable packed cells into the full rectangular table and transports
the exact ordered replay through that injection. The existing array/union-find theorem
then identifies every compiler sigma row with its replayed-cell name. Both captured
keys have kernel certificates for the sigma indices, delta, and chunk stride. The newest
joint statistical theorem and unused-row counterexample construct the fixed and sigma
polynomials and copies from keygen; sigma coherence is derived. Original gate, lookup,
and copy-value validity, public size bounds, and initial selector zeros for the positive
theorem remain premises. Verifier-key column correspondence, instance provenance, and
public commitments remain obligations for the concrete protocol specialization.
The full attempt observer now reuses the existing verifier's message schedule and
retains encoded prefixes, received challenges, the full verifier tape, and a distinct
status for completion, retry, or coincident opening queries. Its success criterion is
exact: every point encodes, x is nonzero, and all round challenges are nonzero. The
x check is equivalent to distinctness of the actual interpolation node lists. No
condition on xi or evaluation-domain membership is added. The same numerical joint
bound holds after this observation, without conditioning on success. The generic
interpreter also proves that appending messages after a failed prefix changes nothing.
The full failure bound is now `(22m+45)/p + (148m+68) bias`. The pre-IPA points
are jointly uniform with ideal blinds, and the IPA identity bound is applied
conditionally on the entire private prefix. The actual proof's point slots are
covered by these families. Wide reduction and the `k+1` actual stopping challenges
supply the stated bound, even at exceptional challenges and without row-correctness
premises. Completion means that the emission schedule finishes, not verifier
acceptance. The successful-view capstone now derives positive normalizers from these
failure and simulation bounds and proves the two-sided conditional budget
`2 epsilon / (1 - B)`, where `B = (42904m+4158)/p + (296m+138) bias`.
The numerical inequality `B < 1` is kernel-certified for `m <= 65535`, including
both captured Action counts; the general endpoint takes that inequality explicitly.
Support certificates are proofs, not witness inputs to the simulator. Independent
selection of completed attempts converges to this conditioned law, also for view
types without a Fintype instance. Separately, every finite independent retry budget
now retains all earlier failed observations, stopping on either completion or the
terminal opening error and continuing only on a retry request. Its two-sided joint
budget is `epsilon / (1 - F)`, where `F` is the honest single-attempt failure bound.
The real and simulated exhaustion probabilities are at most `F^n` and `B^n` and
tend to zero for `B < 1`. The probability recursion is proved equal to the observable
retry program on an independent attempt tape. The witness and statement stay fixed;
fresh private and verifier tapes are required for each attempt. No unlimited-run
history distribution or state-carrying caller equivalence is asserted here.
The deterministic causality interface now proves that a causal message producer stays
causal under the actual observation and failure checks. The checks use only received
challenges. The IPA mask commitment ignores xi, z, and every round challenge; a round
pair depends only on strictly earlier rounds. These facts hold on every private tape,
including zero challenges and invalid openings. The complete staged schedule is now
proved equal to the existing attempt trace, including empty blocks between consecutive
receives. Per-stage dependency facts suffice for causality of that complete trace and
its encoding; the final scalars require no further premise once all challenges agree.
The complete batched decoder now preserves masks, coefficients, blinds, and the IPA
suffix independently of retained-row callbacks. The corresponding full-tape proof
fields satisfy their stage dependencies: advice ignores all challenges, lookup
permutation points use only theta, product points use theta, beta, gamma, the linear
mask ignores all challenges, and quotient pieces add only y. These facts establish
the entire existing attempt prefix before x on the actual complete prover tape.
The evaluation, multi-opening, and IPA stages now satisfy their dependencies on that
same complete tape. The eleven-round adapter uses a challenge-independent `148m+46`
sample count and has exactly the existing wide-reduced reference-prover law. Its
entire message schedule is causal, including the encoded prefixes and actual abort
checks, for every fixed tape and every challenge value. The canonical scalar and point
codecs now instantiate that observer. Each successful item has 32 bytes, and the complete
reference attempt has exactly `2720+2272m` bytes. Its fresh encoded tape law is proved
equal to the existing fresh reference distribution followed by that same observer.
The abstract blinding lemma reduces the hiding bijection to nonidentity in a field
module whose group and scalar field have equal finite cardinalities. The concrete
Vesta instantiation and captured nonidentity checks are pinned separately. The circuit/key
and verifier correspondence remain obligations. The readable budget `epsilon(m) < m*2^-238`
for positive Action counts follows from the sampling bound and kernel integer arithmetic.
The selector-support theorem now covers zero padding outside the compiler's dimensions,
removing the former compiler-domain and fixed-column-count mask premises. The actual
Action specialization supplies canonical public-input rows and compiler fixed/sigma
polynomials and copies. Its prefix, permutation count, and operation-footprint bounds
follow from the existing Action compilation API. The four initial selector zeros and
remaining key/verifier correspondence conditions are explicit. The concrete Action
results have a separate census for their inherited Pallas order dependency.
Fiat–Shamir ZK needs its own argument;
Rust execution correspondence is a separate claim, outside the protocol theorem's target.
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
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPermutationFactorRows_congr
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
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopyChunkWidths
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopyChunkWidths
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
assert_axioms Zcash.Snark.ZeroKnowledge.topLevelSelectorRows_zero_after_placement
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

-- A second valid reference witness follows from inactive selectors and a copy footprint.
assert_computable Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionsCheck +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionsCheck_sound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenPublicPolynomials_inactive_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkInactiveExpressionRowValue_eq
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkInactiveExpressions
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkInactiveExpressions
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnusedAdviceRow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedAdviceRow_usable
assert_computable Zcash.Snark.ZeroKnowledge.plonkUnusedWitness
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_at
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_other_row
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAdviceRotationRow_ne_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_advice_before
assert_axioms Zcash.Snark.ZeroKnowledge.plonkUnusedWitness_expression_before
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenExpressionRowValue_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOriginalRowsValid_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellPair_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyWitness_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygen_exists_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.keygenPlonkReference_no_perfect_simulator
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkKeygen_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkKeygen_distinct_valid_witness

-- The compiler's complete ordered copy stream is packed without dropping any endpoint.
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenConstantCopies_fit
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_rows_lt_usedRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_columns_lt
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyChunkWidths
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellRaw
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellOfFlat
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellOfFlat_raw
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyRaw_bounds
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenFlatCopies +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenCopies +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_encode
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_rows_lt_usedRows
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopies_avoid_unused
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerCopies_exists_distinct_valid_witness
assert_axioms Zcash.Snark.ZeroKnowledge.compilerCopiesPlonkReference_no_perfect_simulator

-- Compiler sigma entries agree with the exact packed replay, not only its cycle classes.
assert_axioms Zcash.Snark.ZeroKnowledge.replayKeygenPermutation_map_apply
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_pair
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCopyCellToFull_copies_encode
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompilerSigmaRow_eq_replay
assert_computable Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaRows +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaRows_eq_replay
assert_computable Zcash.Snark.ZeroKnowledge.plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenSigmaCoherent
assert_axioms Zcash.Snark.ZeroKnowledge.plonkKeygenCopyWitness_of_values
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkCopySigmaIndices
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_plonkSigmaNaming
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_plonkSigmaNaming
assert_axioms Zcash.Snark.ZeroKnowledge.wideCompilerKeygenPlonkVerifier_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.compilerSigmaPlonkReference_no_perfect_simulator

-- Complete protocol attempts: existing schedule, partial encoding, and explicit failure outcomes.
assert_computable Zcash.Snark.ZeroKnowledge.protocolChallengeCount
assert_computable Zcash.Snark.ZeroKnowledge.protocolMessageCount
assert_computable Zcash.Snark.ZeroKnowledge.observeProtocolTrace
assert_computable Zcash.Snark.ZeroKnowledge.protocolTraceBytes
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptTrace
assert_computable Zcash.Snark.ZeroKnowledge.plonkChallengeSequence
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkAfterChallenge +choice
assert_computable Zcash.Snark.ZeroKnowledge.observePlonkAttempt +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptObservation +choice
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_eq_zero_iff
assert_axioms Zcash.Snark.ZeroKnowledge.protocolMessageCount_append
assert_axioms Zcash.Snark.ZeroKnowledge.protocolChallengeCount_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_append_of_failed
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_received_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_received_length
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_of_complete
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_proof_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaTranscript_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkChallengeSequence_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_round
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_opening
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningPointSets_nodup_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_opening_points
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_round
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_all
assert_axioms Zcash.Snark.ZeroKnowledge.observePlonkAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttempt_complete_iff
assert_axioms Zcash.Snark.ZeroKnowledge.wideObservedCompilerKeygenPlonk_simulation_error_bound

-- Full-attempt failure probabilities, including the specified wide-reduced private and verifier tapes.
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointPointFailure
assert_computable Zcash.Snark.ZeroKnowledge.PlonkFailureChallenges +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkFailureChallengeIndex
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptSuccessSet +choice
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPointFamily_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkMaterial_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_preIpa_points
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_ipa_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.idealPlonkJoint_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_no_identity
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_identity_imp
assert_axioms Zcash.Snark.ZeroKnowledge.sampledPlonkVerifier_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.freshSampledPlonkVerifier_identity_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFailureChallenges_cover
assert_axioms Zcash.Snark.ZeroKnowledge.uniformPlonkFailureChallenges_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkFailureChallenges_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttempt_failure_subset
assert_axioms Zcash.Snark.ZeroKnowledge.freshSampledPlonkVerifier_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.freshPlonkAttempt_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.widePlonkAttempt_failure_le

-- Successful full observations: explicit normalizers and the compiler-derived comparison.
assert_computable Zcash.Snark.ZeroKnowledge.plonkAttemptSuccessDecidable +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptFailureBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSuccessfulErrorBound
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonkView
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_eq
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_mono
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCommonFailureBound_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSuccessLowerBound_pos
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_common_failure_le
assert_axioms Zcash.Snark.ZeroKnowledge.plonk_success_support
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonk_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.successfulPlonk_selection_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.wideSuccessfulCompilerKeygenPlonk_simulation_capstone

-- Independent retries retain every prefix and distinguish retry requests from terminal errors.
assert_computable Zcash.Snark.ZeroKnowledge.RetryHistory.prepend
assert_computable Zcash.Snark.ZeroKnowledge.RetryHistory.stopped
assert_computable Zcash.Snark.ZeroKnowledge.RetryHistory.map
assert_computable Zcash.Snark.ZeroKnowledge.runRetryHistory
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_exhausted_iff
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_of_all_retry
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_append_of_stopped
assert_axioms Zcash.Snark.ZeroKnowledge.runRetryHistory_map
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryStep
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries
assert_axioms Zcash.Snark.ZeroKnowledge.retryAttemptTape
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryStep_exhausted
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_exhausted
assert_axioms Zcash.Snark.ZeroKnowledge.eventBias_bind_source
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryStep_source_bias
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryStep_continuation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryError
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryError_eq_sum
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetryError_le
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_uniform_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_exhausted_le
assert_axioms Zcash.Snark.ZeroKnowledge.retainedRetries_exhausted_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFinitePermSetEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteLookupEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteProofString
assert_axioms Zcash.Snark.ZeroKnowledge.plonkFiniteChallenges
assert_computable Zcash.Snark.ZeroKnowledge.plonkRetrySet +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkRetryDecidable +choice
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservedRetrySet
assert_computable Zcash.Snark.ZeroKnowledge.plonkObservedRetryDecidable
assert_computable Zcash.Snark.ZeroKnowledge.runPlonkRetries +choice
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_fromObserved
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_terminal
assert_axioms Zcash.Snark.ZeroKnowledge.runPlonkRetries_complete
assert_axioms Zcash.Snark.ZeroKnowledge.plonkRetry_subset_failure
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_fromTape
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_simulation_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_uniform_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_exhausted
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_both_exhausted_le
assert_axioms Zcash.Snark.ZeroKnowledge.observedPlonkRetries_exhausted_tendsto
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptFailureBound_lt_one
assert_axioms Zcash.Snark.ZeroKnowledge.wideRetriedCompilerKeygenPlonk_simulation_capstone

-- Causality is pointwise on fixed tapes, without excluding failures or zero challenges.
assert_computable Zcash.Snark.ZeroKnowledge.protocolPrefix
assert_computable Zcash.Snark.ZeroKnowledge.ProtocolCausal
assert_computable Zcash.Snark.ZeroKnowledge.ProtocolChecksCausal
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_isPrefix
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_eq_of_count_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_append_of_count_le
assert_axioms Zcash.Snark.ZeroKnowledge.protocolPrefix_append_of_lt_count
assert_axioms Zcash.Snark.ZeroKnowledge.observeProtocolTrace_congr_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.protocolCausal_observation
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAfterChallenge_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProtocolCausal_observation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_maskCommitment_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_messages_agree
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_maskCommitment_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape_withChallenges_messages_agree

-- The exact schedule reduces the full causality theorem to dependencies of its message stages.
assert_computable Zcash.Snark.ZeroKnowledge.protocolStagesTrace
assert_computable Zcash.Snark.ZeroKnowledge.plonkEvaluationStage
assert_computable Zcash.Snark.ZeroKnowledge.plonkPreIpaStages
assert_computable Zcash.Snark.ZeroKnowledge.plonkStageMessages
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_eq_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.protocolStagesTrace_prefix_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptChallenge_prefix_injective
assert_axioms Zcash.Snark.ZeroKnowledge.plonkEvaluationStage_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkStageMessages_challengeCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_eq_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_causal_of_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkObservedPrefix_causal_of_stages
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnConstructor_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnSteps_take_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_take_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_advice_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkTotalColumnRows_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkConstraintModel_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkHonestQuotientPieces_challenges

-- The actual full-tape decoder and all emitted commitments before the evaluation challenge.
assert_axioms Zcash.Snark.ZeroKnowledge.TapeAgrees
assert_axioms Zcash.Snark.ZeroKnowledge.TapeAgrees.eq
assert_axioms Zcash.Snark.ZeroKnowledge.columnTapeCounts_shape
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.columnCoinEquiv_symm_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedTapeCounts_shape
assert_axioms Zcash.Snark.ZeroKnowledge.batchedToColumnTape_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedPreIpaTapeEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.preIpaCoinEquiv_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.batchedPreIpaCoins_shape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkColumnBatches_shape
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPreIpaCoinsEquiv_constructor_irrel
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_coins_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_rows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_before_theta
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_before_products
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaterialFromTape_challenges
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointTape_split_congr
assert_computable Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_coins_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_rows_take
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointMaterialFromTape_congr
assert_computable Zcash.Snark.ZeroKnowledge.plonkProofColumnPoint
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_columnPoint
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_column
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_column_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_column_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_advice_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_lookup_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_products_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_linear
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_piece
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_linear_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_quotient_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkAttemptTrace_prefix_before_x

-- Complete reference-prover causality, with the exact existing sampling law and observation.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_evaluations_congr
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_early_columns
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_linearEval
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_points_q
assert_axioms Zcash.Snark.ZeroKnowledge.plonkMaskViewFromMaterial_groupValues
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_evaluations_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_qPrime_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_groupValues_causal
assert_computable Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkJointViewFromTape_ipa
assert_axioms Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial_mask_agrees
assert_axioms Zcash.Snark.ZeroKnowledge.plonkIpaTranscriptFromMaterial_messages_prefix
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_mask_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_round_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierProofFromTape_stage_causal
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_causal
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_observation_causal

-- Canonical encodings, complete reference proof size, and the exact observed tape law.
assert_axioms Zcash.Snark.ZeroKnowledge.scalarRepresentative_lt_two_pow_256
assert_computable Zcash.Snark.ZeroKnowledge.plonkScalarCodec +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkScalarCodec_length
assert_computable Zcash.Snark.ZeroKnowledge.plonkPointCodec +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_none_iff
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_of_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.plonkPointCodec_length
assert_axioms Zcash.Snark.ZeroKnowledge.protocolMessageCount_flatten
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofString_messageCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_messageCount
assert_computable Zcash.Snark.ZeroKnowledge.encodedPlonkAttempt +choice
assert_axioms Zcash.Snark.ZeroKnowledge.encodedPlonkAttempt_complete_iff
assert_computable Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_law
assert_axioms Zcash.Snark.ZeroKnowledge.freshEncodedPlonkReferenceAttempt
assert_axioms Zcash.Snark.ZeroKnowledge.freshEncodedPlonkReferenceAttempt_law
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceProofFromTape_messageCount
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_proof_length
assert_axioms Zcash.Snark.ZeroKnowledge.plonkReferenceAttemptFromTape_prefix_causal

-- The group argument is abstract here; the concrete Vesta cardinality has its own census.
assert_axioms Zcash.Snark.ZeroKnowledge.scalarBlinding_injective
assert_axioms Zcash.Snark.ZeroKnowledge.scalarBlinding_bijective
assert_axioms Zcash.Snark.ZeroKnowledge.scalarBlinding_bijective_iff

-- The readable bound in the PR follows from the checked numerical budget.
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_le_actions_mul_one
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_one_lt_two_pow
assert_axioms Zcash.Snark.ZeroKnowledge.plonkSimulationErrorBound_lt_actions_mul_two_pow

-- The actual verifier's slot resolution and compression, with grouping order still explicit.
assert_computable Zcash.Snark.ZeroKnowledge.plonkPrivateCommitmentId
assert_computable Zcash.Snark.ZeroKnowledge.plonkOpeningCommitmentIds
assert_axioms Zcash.Snark.ZeroKnowledge.PlonkPublicCommitmentsMatch
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_privateCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkProofFromJointView_quotientCommitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkOpeningCommitmentIds_commitments
assert_axioms Zcash.Snark.ZeroKnowledge.plonkCompressSet_commitment
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_commitmentMembers
assert_axioms Zcash.Snark.ZeroKnowledge.plonkVerifierGroup_commitment
