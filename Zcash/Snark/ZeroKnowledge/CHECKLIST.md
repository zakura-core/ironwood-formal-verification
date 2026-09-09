# ZK checklist and optional extensions

The interactive statistical HVZK theorem is complete for the circuit relation and
random-tape experiment in [ActionCompilerSimulation.lean](ActionCompilerSimulation.lean).
Valid witnesses, the specified setup, and independent uniform random-bit tapes
can remain assumptions of that theorem. The next phase pursues the instantiations
and additional experiments below, without reopening the completed interactive
target. They remain extensions of that target rather than prerequisites for it.
The one-attempt programmable-random-oracle distribution theorem is also complete,
including its fixed-bit simulator. Finite shared-oracle retries, the complete
fixed-request shared-oracle stream, and the finite and unlimited reductions for
a continuing private generator are also checked. The remaining work concerns
witness construction, concrete PRNG and runtime instantiations, and independent
review. The actual Action circuit connection is already proved.

Checked items have the cited proof or validation evidence. Unchecked items are
future work; adding this checklist does not prove them.

| Optional work | What it adds |
| --- | --- |
| Witness and setup corollaries | Applications of the same theorem to a named relation, witness construction, or parameter set. Validity remains a premise. |
| PRNG instantiation | A computational security reduction under a PRNG assumption, with its distinguishing loss recorded separately. |
| Unlimited independent retries | An explicit unlimited-run distribution built from the finite-budget comparisons and vanishing exhaustion tails. |
| Fiat–Shamir ZK | A noninteractive security theorem with oracle access and a stated hash model. |
| Simulator runtime | A costed implementation and running-time bound beyond the existing bit and query budgets. |
| Independent review | An external assessment of the final statements, experiments, and transitive assumptions. |

These are not all strictly stronger guarantees. A concrete setup corollary
specializes a general theorem. A PRNG reduction changes the randomness model and
usually the security notion from statistical to computational. Unlimited retries
extend the execution scope, while Fiat–Shamir changes the interaction and oracle
model. Compare strength only after fixing those models and assumptions.

**Completed interactive target**

- [x] Connect the actual Action circuit, compiler-generated key, masking and degree
  profiles, and selector compression to
  `wideActionCompilerReference_simulation_error_bound` in
  [ActionCompilerSimulation.lean](ActionCompilerSimulation.lean).
- [x] Cover both masking optimizations, independent wide-reduced sampling, complete
  encoded attempts, failure statuses, and message causality. See the
  [development overview](README.md), [sampling law](Randomness.lean), and
  [encoded tape adapter](PlonkEncoding.lean).
- [x] Prove `epsilon(m) < m * 2^-238` for `m >= 1` in
  [PlonkBinaryBounds.lean](PlonkBinaryBounds.lean).
- [x] Pass `lake build --wfail`, including the trust boundaries and endpoint census,
  at baseline commit `f4f6fad2177f3aab24fb9ab23e3cc7b3a96fb7c8`
  (4,179 jobs). Later theorem commits need their own validation.

**1. Valid witnesses: expose the relation and instantiate it**

- [x] Quantify over every witness satisfying the actual original gates, uncompressed
  lookup tuples, and compiler copy equations. The gate and lookup predicate is
  [PlonkOriginalRowsValid](PlonkOriginalRows.lean); the main theorem supplies the
  concrete copy list. This is the validity condition of the proved circuit relation.
- [x] Package these conditions into `ActionZkRelation` and derive
  `wideActionZkRelation_simulation_error_bound` in
  [ActionInstantiation.lean](ActionInstantiation.lean). The caller supplies the
  relation once, and the simulator takes only the setup and public inputs.
- [x] Specify the application-level constructor inputs in
  [ActionWitnessConditions.lean](ActionWitnessConditions.lean), starting from
  [ActionSpec](../../Circuits/Action/Spec.lean). The contract records defined
  Sinsemilla hashes, canonical Merkle children, and scalar representatives that
  fit the current one-field Nat-hint decoder. It derives the existing circuit's
  honest-prover preconditions without assuming successful emission, acceptance,
  or satisfying rows. These constructor conditions do not change the existing
  circuit-level ZK theorem.
- [x] Define the conversion to original advice rows in
  [ActionWitnessRows.lean](ActionWitnessRows.lean). It executes the actual fixed
  witness programs at the circuit-owned V1 placement, starting with compiled
  fixed cells, the declared public inputs, and the concrete application hint
  store. The checked interpreter preserves the exact public statement and
  reconstructs the same compiler environment. The hint and window proofs recover
  all five semantic scalars exactly; this does not yet prove row validity.
- [x] Prove the advice interpreter's dependency theorem and connect its equations
  to the source circuit's complete `ExtendsWitnesses` predicate in
  [AdviceWitnessCausality.lean](AdviceWitnessCausality.lean) and
  [AdviceWitnessEquations.lean](AdviceWitnessEquations.lean). The compiler discharges
  all retained fixed-write and table clauses in
  [CompiledFixedWitnesses.lean](CompiledFixedWitnesses.lean). The current execution
  theorem supplies the distinct-target case; the trace refinement below also
  handles repeated writes.
- [x] Verify the read-support collectors for field, Nat, and Boolean expressions,
  dynamic indexing, local steps, and vector outputs in
  [WitnessReadSupport.lean](WitnessReadSupport.lean) and
  [WitnessProgramSupport.lean](WitnessProgramSupport.lean). The theorem covers all
  branches and arithmetic values; native callbacks still require their own
  semantic read certificates. [WitnessBuilderSupport.lean](WitnessBuilderSupport.lean)
  extends these support proofs to the original scalar, Nat, Boolean, and value
  builders, and [AdviceReadPlan.lean](AdviceReadPlan.lean) checks structured reads
  against the preceding assignments.
- [x] Prove preservation of previously assigned values across repeated writes in
  [AdviceWitnessTrace.lean](AdviceWitnessTrace.lean). The checked alias plan in
  [AdviceAliasPlan.lean](AdviceAliasPlan.lean) permits a repeated target only for a
  source-certified copy with the same established value. Its theorem establishes
  the original full witness equations without assuming distinct targets.
- [x] Certify the original native base-coordinate callbacks through each round,
  arbitrary-length loops, and the full multiplication region in
  [NativeMulCopySupport.lean](NativeMulCopySupport.lean). Instantiate the exact
  Action base columns and separation in
  [ActionMulNativeCopies.lean](ActionMulNativeCopies.lean). Structured programs
  supply their copy sources through [WitnessCopySemantics.lean](WitnessCopySemantics.lean).
- [x] Connect native copy annotations to the complete original Action in
  [ActionNativeRouting.lean](ActionNativeRouting.lean). The checked source schedule
  places the shared-base multiplier at region 297; all other regions have no
  native annotations. `actionAdviceAliasPrograms_sources` proves the exact
  evaluator semantics of every collected copy annotation, including structured IR.
- [x] Certify the original native witness functions' read dependencies through
  [WitnessFunctionSupport.lean](WitnessFunctionSupport.lean), with proofs for
  [Poseidon](PoseidonWitnessSupport.lean),
  [incomplete multiplication](MulIncompleteWitnessSupport.lean),
  [fixed-base multiplication](FixedBaseWitnessSupport.lean),
  [fixed-base canonicity](FixedCanonicityWitnessSupport.lean),
  [note commitment](NoteWitnessSupport.lean),
  [note canonicity](NoteCanonicityWitnessSupport.lean),
  [CommitIvk](CommitIvkWitnessSupport.lean),
  [Sinsemilla](SinsemillaWitnessSupport.lean),
  [Merkle layers](MerkleWitnessSupport.lean), and
  [scalar wrappers](NativeScalarWitnessSupport.lean). Nested callbacks retain
  explicit support premises. These are semantic certificates for the original
  functions, not yet a certificate enumerating every Action occurrence.
- [x] Retain equality of the immutable public and fixed environment in native
  support certificates. This certifies the original absolute-row `instanceGet`
  reads without treating their rows as region-relative advice cells. The execution
  bridge already supplies this equality. Regression checks accept a public read
  at nonzero placement and reject agreement between changed public inputs.
- [x] Prove that the [fixed Action hint programs](ActionHintReadSupport.lean),
  every scalar window, and the original Merkle sibling and swap callbacks read
  no cells. Their values depend on the immutable hint store.
- [x] Connect certified native and structured annotations to the witness equations
  in [AdviceSupportPlan.lean](AdviceSupportPlan.lean). A successful availability
  check proves causality; exact source erasure, semantic copy provenance, and
  a successful alias check then imply the original `ExtendsWitnesses` predicate.
  The [alias-map refinement](AdviceAliasMapPlan.lean) and
  [read-map refinement](AdviceSupportMapPlan.lean) now preserve all original
  checker results, including rejection. Their map representation retains column
  kind, index, and signed row, and supplies the same witness-equation theorem.
- [x] Keep read annotations and original copy tags in one
  [source-indexed certificate](AdviceSourceCertificate.lean). Proven source
  equalities change proof metadata while retaining directly evaluable scan data;
  generation supplies semantic read proofs and preserves every original instruction.
- [x] Bound certificate-generation pieces with
  [synchronous kernel checks](../../Meta/CertificateChunks.lean). Each checked
  continuation retains its exact source and remaining certificate type; composition
  preserves all source equations. Source-list and advice regressions force piece
  boundaries, including parameterized opaque producers and rejected annotations.
  This controls proof-generation resources; the complete Action scans remain below.
- [x] Split the global read and alias scans into
  [checked map transitions](AdviceMapScan.lean), preserving every result of the
  original policies. The [bounded elaborator](../../Meta/AdviceMapScan.lean)
  stores kernel-checked intermediate maps and composes checked continuations.
  Regression checks force a boundary at every entry and reject unavailable
  reads, fresh-write collisions, and conflicting alias roots across boundaries.
  The complete Action scan still has to run successfully.
- [x] Certify the original [eight-region witness-loading stage](ActionWitnessLoadCertificate.lean),
  including all eleven source instructions and both finite scans at the proved
  Action placement. The certificate is a kernel-evaluated proof artifact.
- [x] Certify all 1,083 original instructions of the
  [value-commitment stage](ActionValueWitnessCertificate.lean), for arbitrary stage
  inputs. The certificate includes the short multiplication, full-width blinding
  multiplication, and complete addition. Structured wrappers retain all IR read
  dependencies; the complete Action scan must still establish their availability.
- [ ] Build the certified annotations for the complete Action and discharge its
  global alias and read-plan checks. Derive `ExtendsWitnesses` for the final
  assignment.
- [x] Identify the exact private readings of the original completeness preconditions
  in [ActionWitnessReadings.lean](ActionWitnessReadings.lean): eight fields, six
  points, five scalar/window pairs, and 32 Merkle readings. Agreement preserves
  those preconditions; unused decomposition exports and auxiliary tail readings
  need no equality. The stronger observation interface remains available in
  [ActionWitnessObservation.lean](ActionWitnessObservation.lean).
- [x] Recover those readings from the original witness equations in
  [ActionWitnessExtraction.lean](ActionWitnessExtraction.lean), using the original
  [field and point loaders](ActionDirectHintExtraction.lean),
  [scalar routing](ActionScalarHintExtraction.lean), and
  [Merkle calls](ActionMerkleHintExtraction.lean). The proof uses the actual
  generated assignment and fixed hint program, with the already stated scalar
  representability bounds.
- [x] Transfer the recovered readings and preserved public inputs to the original
  completeness theorem in [ActionWitnessCompleteness.lean](ActionWitnessCompleteness.lean).
  It proves the original operation constraints once the complete source certificate
  supplies the witness equations; it adds no construction precondition.
- [x] Prove the [converse gate compiler laws](CompiledGateCompleteness.lean),
  using checked positive selector degree and an explicit finite activation-coverage
  condition. [Direct source labels](DirectGateLabels.lean) preserve gate names as
  well as selector indices, including gates sharing a selector.
- [x] Interpret the [actual Action query feeds](ActionQueryRows.lean) in the generated
  environment, including the signed row-zero read. The [advice footprint](AdvicePlacementBounds.lean)
  and [arbitrary-feed valuation](ActionQueryValuation.lean) also cover the unused
  final domain row through [inactive gate equations](InactiveGateCompleteness.lean).
- [x] Prove that the original operation constraints imply the
  [complete ordered compiler copy stream](CopySourceCompleteness.lean), including
  positional constant allocations and their actual fixed-column values.
- [x] Identify every prover permutation-cell value with its original compiler
  endpoint in [ActionCopyValues.lean](ActionCopyValues.lean), using the exact
  instance, advice, and fixed query routes. The original operation constraints
  then imply every packed copy equation.
- [x] Carry source lookup tuples through selector compression and the actual
  verifier queries in [CompiledLookupCompleteness.lean](CompiledLookupCompleteness.lean)
  and [ActionLookupValues.lean](ActionLookupValues.lean). Active rows retain an
  explicit source-coverage premise; inactive rows select their proved actual
  [zero-index table entry](ActionLookupFallback.lean), including Sinsemilla's
  nonzero coordinate values.
- [x] Derive all actual Action gate rows in [ActionGateValues.lean](ActionGateValues.lean)
  and preserve gate and paired lookup relations through the reference-key shape
  in [ActionRowRelations.lean](ActionRowRelations.lean).
- [x] Compose the gate, lookup, and actual packed-copy bridges into
  `ActionZkRelation` in [ActionConstraintsRelation.lean](ActionConstraintsRelation.lean).
  This intermediate theorem takes original operation constraints and the two
  explicit activation-coverage checks; the complete source certificates must
  still supply those premises for the application constructor.
- [ ] Discharge the complete witness equations and the actual gate and lookup
  activation-coverage checks.
- [ ] Package that evidence as `ActionZkRelation` and derive application-level
  interactive and one-attempt oracle simulation corollaries.

Closure: the application theorem takes a valid Action witness and constructs the
row-validity evidence. Validity remains a hypothesis; the existing circuit-level
ZK theorem already handles all witnesses in its relation.

**2. Setup: specialize the public parameters**

- [x] Derive the Action key from the actual compiler. The remaining setup premises
  are `urs.k = 11` and `urs.w != 0` in the main theorem.
- [x] Prove nonidentity of all four captured blinding points in
  [CapturedBlinding.lean](CapturedBlinding.lean). The captured URS definitions
  [set `k` to eleven](../Fixtures/SingleAction/Honest/Fixture.lean).
- [x] Add `wideCapturedActionZk_simulation_error_bound` for `capturedActionURS`,
  supplying both setup proofs from its definition and nonidentity certificate in
  [ActionInstantiation.lean](ActionInstantiation.lean).
- [x] Record the scope of that setup: it names the one-Action honest fixture's
  captured URS, used for any Action count. It claims a captured parameter set;
  no parameter-generation procedure is asserted.

Closure: the specialized theorem requires no caller-supplied setup proofs. The
existing inherited Pallas and Vesta curve-order certificates remain recorded in
the [Action trust boundary](Action/TrustBoundary.lean).

**3. Randomness: retain the statistical model and state any PRNG instantiation**

- [x] Prove the distribution of independent uniform 512-bit words reduced modulo
  `p`, its bias, the exact private draw count, and the reference tape adapter's law.
  See [Randomness.lean](Randomness.lean), [PlonkTape.lean](PlonkTape.lean), and
  [PlonkEncoding.lean](PlonkEncoding.lean).
- [x] Add a complete raw-tape source, sampled independently of the verifier coins
  for each fixed statement and witness. Prove exact agreement with the reference
  under uniform raw bits and an `epsilon(m) + eta` bound under joint source error
  `eta` in [ActionRandomnessSource.lean](ActionRandomnessSource.lean). Marginal
  per-sample bounds alone do not establish this whole-tape premise.
- [x] Parameterize one attempt by a generator, seed law, and raw tape of exactly
  `148m + 46` 512-bit draws. Prove the test-dependent reduction in
  [PrngReduction.lean](PrngReduction.lean) and its concrete
  [Action corollary](ActionPrng.lean). One seed supplies one complete tape;
  repeated generator state is outside this one-attempt statement.
- [x] Expose the required PRNG-test advantage bound and prove the final
  `epsilon(m) + eta` comparison for arbitrary probabilistic Boolean view tests.
  This assumes a bound for the actual reduction, not statistical closeness of
  the entire PRNG output tape.
- [x] Define the concrete PRNG game in [PrngSecurity.lean](PrngSecurity.lean), with
  an explicit uniform bit-seed length, complete output type, and supplied
  admissible distinguisher class. Sample retained auxiliary data independently of
  the seed. Bound the test's acceptance advantage in both directions, rather than
  the statistical distance of the generated tape.
- [x] Instantiate that game with the existing Action reduction in
  [ActionPrngSecurity.lean](ActionPrngSecurity.lean). Prove exact equality of the
  actual distinguishing experiments and the `epsilon(m) + eta` bound. Membership
  of the complete prover-and-test reduction in the admissible class is an explicit
  premise. Discharging it from runtime bounds remains in section 6; no concrete
  generator security or efficiency theorem is asserted here.
- [x] Define continuous generator state and prove its finite replay law in
  [GeneratorTape.lean](GeneratorTape.lean), [GeneratedRetryCoins.lean](GeneratedRetryCoins.lean),
  and [ActionGeneratorRetry.lean](ActionGeneratorRetry.lean). Each started attempt
  consumes one full `148m + 46`-word block; unused words in that block are discarded.
  Terminal results stop before another block is allocated. The private final state
  advances by the number of started attempts times that width, with no reseeding.
  It is not part of the verifier's observed output.
- [x] Prove the full finite Fiat–Shamir computational reduction in
  [ActionOracleRetryPrng.lean](ActionOracleRetryPrng.lean) and instantiate the
  continuing-generator execution in [ActionGeneratorPrng.lean](ActionGeneratorPrng.lean).
  One fresh seed follows adaptive preprocessing; the same oracle cache survives
  retries and postprocessing. The tested observation has error at most
  `error_retry(m,q_pre,n) + eta`, where `eta` covers the complete generated prefix
  and the admitted retry-and-postprocessing reduction. Its exact capacity is
  `512 * n * (148m + 46)` bits, with the checked encoding in
  [ActionPrivateRetryBits.lean](ActionPrivateRetryBits.lean). No independence of
  generated attempt blocks is assumed. Concrete PRNG security and reduction-class
  membership remain premises; this is a finite-budget computational reduction.
- [x] Define the complete seeded Action stream and prove its exact finite
  continuing-generator projections in [ActionGeneratorStream.lean](ActionGeneratorStream.lean).
  The private generator is initialized once; the independent public reply stream
  drives the existing cached execution, with the fixed request and all public
  cache updates retained. [ActionGeneratorStreamPrng.lean](ActionGeneratorStreamPrng.lean)
  proves two-sided tested error `2 * (C(m,q) + b(m)^n + eta)` for an unlimited
  run, using the whole-prefix PRNG assumption at cutoff `n`. Both the clipped-view
  reduction and the finite exhaustion detector must belong to the stated
  admissible class. [ActionOracleRecordedPrng.lean](ActionOracleRecordedPrng.lean)
  bounds the actual generated exhaustion tail by `b(m)^n + C(m,q) + eta`;
  [ActionGeneratorStreamTermination.lean](ActionGeneratorStreamTermination.lean)
  proves the same nontermination bound without testing the infinite event in the
  PRNG game. No independence of generated blocks or almost-sure seeded termination
  is assumed. This fixed-request result does not instantiate adaptive before/after
  processing on the infinite stream or discharge the concrete PRNG/runtime premises.

Closure: the uniform-bit theorem stays statistical. A PRNG-backed result is
conditional on the stated PRNG security and generally gives a computational ZK
claim. The wide-reduction proof alone establishes neither uniform PRNG output nor
independence. A particular Rust implementation is a separate correspondence target.

**4. Unlimited independent retries: construct the limiting experiment**

- [x] Define the observable retry policy and its finite-tape execution in
  [RetryHistory.lean](RetryHistory.lean). Prove a uniform two-sided comparison and
  vanishing exhaustion tails in [RetryHistorySimulation.lean](RetryHistorySimulation.lean).
- [x] Construct a normalized distribution of complete stopped histories for an
  unlimited stream of independent attempt tapes, keeping the statement and witness
  fixed. Retain every failed prefix, received challenge, verifier tape, and status.
  Retry only a request for fresh randomness; completion and terminal errors stop.
  [RetryTape.lean](RetryTape.lean) gives the normalized stopped-tape weights;
  [RetryFlow.lean](RetryFlow.lean) proves the independent one-step policy.
- [x] Prove exact finite-budget projections in [RetryProjection.lean](RetryProjection.lean)
  and almost-sure termination when `B(m) = F(m) + epsilon(m) < 1`. The geometric
  length tails tend to zero. [RetryExpectation.lean](RetryExpectation.lean) proves
  expected attempts `1 / (1 - r)` for actual retry probability `r`.
- [x] Lift the finite uniform comparison to every event of the unlimited history
  distribution, with two-sided error at most `epsilon(m) / (1 - F(m))`, in
  [RetryLimit.lean](RetryLimit.lean).
- [x] Instantiate that result with the current Action compiler theorem, canonical
  codecs, and numerical failure bounds in [ActionRetryLimit.lean](ActionRetryLimit.lean).
  Expected attempts are at most `1 / (1 - F(m))` for the prover and
  `1 / (1 - B(m))` for the simulator. The capstone supplies `B(m) < 1` from the
  checked condition `m <= 65535`, without asserting a protocol maximum. It uses
  the closed Action masking profile and relation.

Closure: a checked theorem compares the complete unlimited-run histories under the
independent-attempt policy, including terminal errors. Termination alone does not
establish verifier acceptance.

**5. Fiat–Shamir: prove simulation with transcript-derived challenges**

- [x] Recover the exact raw 512-bit response distribution conditional on each
  wide-reduced field challenge, using a bounded quotient in
  [DigestFiber.lean](DigestFiber.lean). Prove the joint tape law in
  [DigestTape.lean](DigestTape.lean), and retain the same `epsilon(m)` for the
  complete typed Action view with raw responses in [ActionDigest.lean](ActionDigest.lean).
- [x] Define and prove injectivity of the scalar, affine-point, and marker byte
  encoding in [TranscriptBytes.lean](TranscriptBytes.lean). Include the specified
  personalization, digest reduction, and first statement-prefixed query in
  [ByteFiatShamir.lean](ByteFiatShamir.lean). Point-emission checks remain the
  observer's responsibility; this total encoding does not permit an identity
  point to bypass them.
- [x] Define a lazy cached oracle with exact tape semantics in
  [CachedOracle.lean](CachedOracle.lean). Prove that programming preserves all
  stored answers and that its two-sided error is at most the independent
  experiment's conflict probability in [OracleProgrammingBias.lean](OracleProgrammingBias.lean),
  including private-randomness mixtures. [OracleResources.lean](OracleResources.lean)
  bounds query-trace length and cache growth; these are not running-time bounds
  for arbitrary supplied computations.
- [x] Define real and simulated noninteractive experiments with a classical,
  query-bounded random-oracle adversary in
  [ActionOracleAdversary.lean](ActionOracleAdversary.lean). One attempt follows
  adaptive selection of a valid statement/witness pair and arbitrary auxiliary
  state. The simulator erases the witness; oracle access continues after the
  proof with the same retained table. Private prover tapes are sampled freshly
  after selection, independently of the preceding execution.
- [x] Connect the reference message sequence to
  [the verifier's Fiat–Shamir schedule](../Verifier/FiatShamir.lean), including the
  verifying-key representation, public-instance prefix, domain separators, canonical
  point/scalar encoding, squeeze order, and digest-to-field conversion. The
  [online reference driver](PlonkOracle.lean) uses the existing causality theorem
  and abort checks. [PlonkQuerySchedule.lean](PlonkQuerySchedule.lean) seals all
  twenty-two queries; [ActionFiatShamir.lean](ActionFiatShamir.lean) supplies the
  actual Action instance prefix and specified total coordinate encoding.
- [x] Apply the cached-oracle programming theorem to the witness-free Action
  simulator and actual challenge schedule in
  [ActionOracleModel.lean](ActionOracleModel.lean). The
  [first advice commitment is exactly uniform](PlonkAnchor.lean) and anchors
  every query. [ActionOracleConflicts.lean](ActionOracleConflicts.lean) proves
  no internal query repeats and bounds all prior-query conflicts by `q_pre / p`.
- [x] Compose with the joint PLONK and IPA simulation and exceptional-event bounds.
  [SimulationAgreement.lean](SimulationAgreement.lean) charges the existing
  `epsilon(m)` once. The complete one-attempt oracle experiment has two-sided
  error `epsilon(m) + q_pre / p`, including incomplete attempts and simulator
  programming failure, for `m > 0`.
- [x] State the resulting one-attempt simulation theorem for the proof and the
  adversary's final oracle view in [ActionFiatShamir.lean](ActionFiatShamir.lean).
  The [computable simulator](ActionOracleSimulator.lean) has exactly that law,
  with 22 raw challenge words and `132m + 36` uniform field draws.
  [ActionOracleResources.lean](ActionOracleResources.lean) bounds both final
  caches by `q_pre + 22 + q_post`. These are primitive sampling and oracle-query
  budgets; machine-instruction and bit-sampler time bounds are not formalized.
  Relating concrete BLAKE2b to the random oracle remains a cryptographic modeling
  assumption, and the real prover retains its wide-reduced sampling law.
- [x] Give the simulator a fixed uniform bit tape, eliminating its ideal-field
  sampling primitive. [RawBits.lean](RawBits.lean) packs the bits explicitly;
  [ActionOracleBits.lean](ActionOracleBits.lean) executes the simulator on
  `512 * (132m + 58)` bits. Its `132m + 36` private reductions add that many
  `delta` terms. [ActionFiatShamirBits.lean](ActionFiatShamirBits.lean) proves the
  full adaptive oracle comparison and retained cache budget for this implementation.
  [OracleBitBounds.lean](OracleBitBounds.lean) checks the resulting bound
  `(42882m + 4113 + q_pre) / p + (280m + 106) delta < m * 2^-238 + q_pre / p`
  for `m >= 1`. The earlier simulator keeps its sharper bound; these additional
  sampling costs belong only to the new simulator distribution. Fixed bit-input
  length does not assert a machine-instruction running-time bound.
- [x] Define finite retained-history retries with a shared oracle cache, fresh
  private randomness per attempt, and a fixed statement and witness. Retry only
  `retryRandomness`; completion, terminal opening errors, and simulator programming
  failure stop. Keep all preceding observed failures and the final cache. See
  [StatefulRetry.lean](StatefulRetry.lean), [OracleRetry.lean](OracleRetry.lean),
  and the [Action retry implementation](ActionOracleRetry.lean).
- [x] Prove the shared-cache transition and history laws, including the cache
  budget through every attempted proof. Preserve adaptive preprocessing and
  postprocessing in the same oracle experiment.
  [OracleRetryTape.lean](OracleRetryTape.lean) proves exact deterministic tape
  replay; [ActionOracleRetryResources.lean](ActionOracleRetryResources.lean)
  proves persistent answers and cache growth. Preprocessing selects one fixed
  request; the internal retry run has no intervening adversary queries.
- [x] Derive the two-sided statistical comparison for every finite attempt budget,
  including prior-query conflicts, internal retry-cache growth, simulator sampling
  bias, and explicit exhaustion. [ActionFiatShamirRetry.lean](ActionFiatShamirRetry.lean)
  gives `n * epsilon_bits(m, q_pre) + 11n(n-1)/p`; the final cache has at most
  `q_pre + 22n + q_post` entries. [OracleRetryBounds.lean](OracleRetryBounds.lean)
  checks the formula and its binary bound. The comparison charges all available
  attempts and assumes no independence of retry decisions or shared-oracle
  termination theorem.
- [x] Define the complete observed stream for unlimited shared-oracle retries in
  [ActionOracleStream.lean](ActionOracleStream.lean), retaining every result,
  intermediate cache, and possible infinite run. For a fixed valid request and
  any prior cache of length at most `q`,
  [ActionOracleStreamSimulation.lean](ActionOracleStreamSimulation.lean) compares
  every measurable event in both directions with error
  `C(m,q) = 2 * epsilon_bits(m, q + 22)`, assuming the uniform simulator retry
  rate `b(m) = B(m) + (132m + 36) delta` is at most `1/2`.
  [ActionOracleRetryGeometric.lean](ActionOracleRetryGeometric.lean) supplies this
  condition for `1 <= m <= 65535`, without asserting a protocol maximum. The
  finite-prefix bound is uniform in the budget; the cylinder limit adds no loss
  and makes no real-termination assumption. There are no intervening adversary
  queries during the run. [ActionOracleStreamTermination.lean](ActionOracleStreamTermination.lean)
  proves almost-sure simulator termination, real nontermination mass at most
  `C(m,q)`, and truncation errors `b(m)^n` and `b(m)^n + C(m,q)`, respectively.

Closure for one attempt: the classical programmable-random-oracle distribution
theorem, its computable simulators, and their sampling/query budgets are checked,
including a simulator driven by a fixed uniform bit tape.
The interactive HVZK theorem and its causality proof are inputs to this separate
oracle argument. The finite adaptive shared-oracle extension and complete
fixed-request shared-oracle stream are also checked, together with the conditional
unlimited seeded reduction in item 3. Runtime analysis remains separate.

**6. Simulator runtime: connect resource counts to execution cost**

- [x] Provide a computable simulator with a fixed uniform bit-input length and
  checked oracle-cache bounds in [ActionOracleBits.lean](ActionOracleBits.lean).
- [x] Specify and implement structural costs for byte equality and the cache
  phase on materialized query logs. [ByteEqualityCost.lean](ByteEqualityCost.lean),
  [OracleCacheCost.lean](OracleCacheCost.lean), and
  [OracleProgrammingCost.lean](OracleProgrammingCost.lean) prove exact cost erasure
  and retain work on every collision branch. The actual transcript's
  [byte-size bound](TranscriptByteSize.lean) and
  [PLONK schedule bound](PlonkTranscriptSize.lean) give the
  [Action cache-phase bound](ActionCacheCost.lean):
  `22 * ((q + 22) * (9490m + 14207) + 4) + 2` for `m` Actions and `q` initial
  cache entries. Constructing the view remains outside this component's cost.
- [x] Give exact counted implementations of
  [little-endian bit packing](RawBitPackingCost.lean) and
  [wide field reduction](WideBitReductionCost.lean). Both retain the complete
  supplied bit-reader cost and prove equality with the simulator's existing tape
  conversion. A 512-bit word costs at most `512R + 264193` structural units when
  each input read costs at most `R`. The model charges bounded-width arithmetic
  and reader-index adapters; whole-tape access and simulator composition remain open.
- [x] Construct and fully materialize the counted [IPA simulator](IpaSimulatorCost.lean),
  with exact erasure to the existing transcript. The bound includes the complete
  supplied input accesses, both [public folds](PublicFoldCost.lean), the
  [scalar case test](IpaScalarCost.lean), all round points and commitment arithmetic,
  and both responses. It covers every challenge value and does not leave work
  hidden behind function-valued transcript fields.
- [x] Construct and fully materialize the counted [PLONK mask view](PlonkMaskSimulatorCost.lean),
  including every commitment-point multiplication, every five-field observation
  vector, and both extra scalars. Erasure is the existing simulator's complete
  finite view, with all coin and setup-reader costs retained.
- [x] Count the actual [expression evaluator](ExpressionCost.lean),
  [lookup compression](ExpressionCompressionCost.lean), all five
  [lookup constraints](LookupExpressionsCost.lean), and both
  [permutation-chunk folds](PermutationChunkCost.lean), preserving their original
  results and all supplied query-reader costs.
- [x] Count the [complete permutation constraints](PermutationExpressionsCost.lean),
  including first, last, and inter-set boundaries. Compose gates, permutations,
  and lookups into the exact [per-sub-proof list](ConstraintAssemblyCost.lean)
  and [complete multi-Action list](ConstraintCollectionCost.lean). The bounds retain
  the materialized input sizes, preparation costs, and concatenation work.
- [x] Count the [Lagrange basis values](LagrangeBasisCost.lean), signed field powers,
  [quotient evaluation fold](QuotientEvaluationCost.lean), and
  [scalar query routing](QueryRoutingCost.lean), including out-of-range zero defaults.
  Their complete query-provider and quotient composition is recorded below.
- [x] Count both [Lagrange interpolation loops](LagrangeEvaluationCost.lean) and
  the complete [multi-opening scalar evaluation](MultiopenEvaluationCost.lean),
  preserving coincident-point division and missing-evaluation defaults. The
  [counted commitment/scalar combination](MultiopenCombinationCost.lean) is
  proved equal to evaluating the original symbolic MSM construction.
- [x] Count construction of the actual [private-column schedule](PrivateColumnOrderCost.lean),
  its equality search, and [disclosed-value routing](PrivateColumnRoutingCost.lean).
  The [commitment-entry readers](CommitmentEntryCost.lean) preserve every column,
  linear-mask, quotient-piece, and quotient-prime slot. Bounds include complete
  supplied entry costs; missing columns retain their original zero fallback.
- [x] Construct the actual [public and private opening layouts](OpeningGroupLayoutCost.lean)
  and [fixed/advice query tables](QueryOrderCost.lean), with exact source-order
  identities. [Private opening evaluations](PrivateOpeningEvaluationCost.lean)
  include column routing and the full Horner fold. The complete
  [public first-group claims](PublicOpeningClaimsCost.lean) include row-polynomial
  preparation and actual fixed-query routing. The
  [collapsed quotient point](CollapsedQuotientPointCost.lean) counts all eight
  piece reads, power loops, and group operations.
- [x] Reconstruct and materialize all five [opening commitments](OpeningCommitmentVectorCost.lean),
  including full public polynomial preparation and every private group fold.
  The [node and group-value vectors](OpeningScalarVectorsCost.lean) retain all
  routed scalar reads and original node counts. The [point-set construction](OpeningPointSetsCost.lean)
  counts the original products, inverses, sixth power, and node-index routing.
- [x] Compose that preparation into the [complete public opening](PublicOpeningCost.lean)
  and prove its [total cost bound](PublicOpeningCostBound.lean). Erasure is the
  reference public opening after evaluation of its symbolic MSM. The algorithm
  includes interpolation, the final point/scalar fold, every materialized input
  list, and all supplied reader costs. The supplied quotient scalar's computation
  is accounted for by the complete quotient calculation below.
- [x] Construct the [original claim queries](PlonkClaimQueriesCost.lean),
  [permutation inputs](PermutationQueryPreparationCost.lean), and
  [lookup inputs](PlonkLookupInputsCost.lean), retaining their full preparation
  costs. [Input bounds](PlonkClaimInputBounds.lean) derive stored-field access,
  chunk sizes, and lookup-tree sizes from those constructors.
- [x] Compose those providers into the exact
  [complete claim constraint list](PlonkClaimConstraintsCost.lean) and its
  [total cost bound](PlonkClaimConstraintsCostBound.lean). The actual key trees
  and column layout determine the budget; provider correctness and output sizes
  are proved, rather than supplied as separate constraint-budget premises.
- [x] Compute the [complete inferred quotient](PlonkVerifierHxCost.lean),
  including domain powering, all basis values, input and constraint preparation,
  list materialization, and the final fold and division. Its
  [cost bound](PlonkVerifierHxCostBound.lean) retains every supplied row, key,
  observation, and challenge cost. Erasure is the existing `plonkVerifierHx`,
  including exceptional field values. Concrete stored public-input and setup
  representations, encoding, and whole-simulator composition remain below.
- [x] Count loading canonical polynomial coefficients, their
  [Horner evaluation](PolynomialArithmeticCost.lean), and the full generator sweep
  and ordered claim folds in [CommitmentArithmeticCost.lean](CommitmentArithmeticCost.lean).
  The erasure proofs identify the existing polynomial and commitment operations;
  constructing the input polynomials remains separate work.
- [x] Construct [public row coefficients](RowCoefficientCost.lean) by a counted
  inverse DFT and prove agreement with the canonical interpolant on the specified
  power-of-two domain. [Row evaluation and commitment](RowPolynomialCost.lean)
  include this coefficient preparation, every input read, and every generator
  access. Concrete stored public-row readers are recorded below.
- [x] Represent supplied [setup vectors](StoredPlonkSetupCost.lean),
  [key trees and layouts](StoredPlonkKeyCost.lean), and
  [Action public inputs](ActionPublicInputCost.lean) as materialized data.
  [Row and finite-vector readers](StoredRowsCost.lean) count both matrix traversals,
  preserve zero defaults, and recover the original finite families. Setup generation
  is outside these supplied-input read bounds. Expression evaluation retains the
  cost of traversing stored trees after their references have been read.
- [x] Read the [complete stored bit tape](StoredBitTapeCost.lean) with every list
  traversal and word-index calculation counted. Materializing all raw words or all
  reduced fields is exactly the existing fixed-tape conversion, with a polynomial
  bound in the word count and stored bit length. The complete simulator still needs
  to compose this conversion with its challenge/private-tape routing.
- [x] Compose the [complete algebraic joint simulator](PlonkJointSimulatorCost.lean):
  materialized PLONK masks, stored observation and point readers, the complete
  inferred quotient, public opening, and every IPA output. Erasure is the existing
  joint simulator's complete finite view. The [total cost theorem](PlonkJointSimulatorCostBound.lean)
  derives all generated-reader bounds from the mask constructor and holds at every
  challenge value. It has no unpriced expected-quotient callback.
- [x] Instantiate those public readers using the
  [stored Action adapter](StoredActionJointCost.lean) and its
  [concrete bound](StoredActionJointCostBound.lean). Public-row, generator, and
  setup-read premises follow from the original Action input layout and stored
  dimensions. Challenge/private-coin producers, proof-field routing, encoding,
  and transcript observation remain to be composed with the fixed-bit stage.
- [ ] Specify the runtime model and input representations, including access to
  public inputs and setup, bit packing, field reduction, group arithmetic,
  polynomial operations, transcript encoding, and cache lookup/programming.
- [ ] Build costed implementations of those operations and prove that erasing
  their costs gives the operations used by the existing simulator. Account for
  supplied callbacks instead of assigning arbitrary host computations zero cost.
- [ ] Compose the costed operations into the actual fixed-bit simulator and prove
  equality with `actionOracleSimulatorFromBits`, retaining all failure branches.
- [ ] Prove the resulting running-time bound in the Action count, prior cache
  size, and explicit input sizes. State primitive-cost assumptions and distinguish
  a cost-model theorem from compiler or machine-code correspondence.
- [ ] Discharge the PRNG reduction's resource conditions wherever that
  computational instantiation is claimed. This requires bounds for the actual
  real-prover-and-test reduction, including retained auxiliary data and any retry
  or postprocessing work; the simulator's runtime bound alone does not supply them.

Closure: a bound on the same simulator's execution cost follows from a specified
cost model and explicit primitive assumptions. Computability and a fixed random
tape alone do not prove that running-time statement.

**7. Review: prepare the evidence and obtain independent assessment**

- [x] Prepare [the review packet](REVIEW.md), mapping each current claim to its
  exact theorem, real/simulated experiment, validity/setup/randomness assumptions,
  error formula, failure policy, and runtime scope. It records an exact proof
  baseline and links its validation and declaration inventories.
- [x] Locally check that the recorded theorem inputs and public observations match
  those claims, including auxiliary data, retained prefixes, oracle state, finite
  exhaustion, and the private generator-state boundary. This is a local scope check.
- [x] Recheck transitive dependencies and every new declaration pin at that proof
  baseline. The recorded inventories identify every direct pin and transitive
  native owner; the development retains the inherited named curve-order
  certificates and no admitted lemma.
- [ ] Obtain independent review of the packet and record the reviewed commit,
  findings, resolutions, and remaining qualifications. A local self-review or
  passing Lean build does not complete this item.

**Validation and review if an extension is pursued**

- [x] Build changed modules and their dependent trust boundaries; run the required
  endpoint and axiom checks. Pin every new logical declaration, including helpers
  outside the endpoint-name census. All completed milestones have these checks.
  The repeated-write and Action copy-source milestone inventories 91 declarations
  and passes the 326-endpoint census. Its source-specific declarations use the
  existing Pallas curve-order certificate; it introduces no native certificate.
  The byte-cache cost milestone inventories 31 declarations across seven modules,
  each with one direct pin. Its Action corollaries retain the existing Pallas and
  Vesta curve-order owners; the milestone introduces no native certificate.
  The compiler/query checkpoint passes the [focused 3,691-job build](review/validation-6fba8271.log),
  with 57 declarations across eleven modules directly pinned, nine source-list
  regressions and fourteen advice-source regressions checked, and both original
  stage certificates rebuilt. The Action row checkpoint passes the
  [focused 3,700-job build](review/validation-fb1c737e.log), with
  [35 declarations across nine modules](review/axioms-fb1c737e.log) directly pinned
  and separately inventoried. The arithmetic milestone passes the
  [focused 3,728-job build](review/validation-1e80ffcc.log), with
  [118 declarations across fourteen modules](review/axioms-1e80ffcc.log) directly
  pinned and separately inventoried. The constraint checkpoint passes the
  [focused 3,739-job build](review/validation-c55b3ea1.log), with
  [80 declarations across ten runtime modules](review/axioms-c55b3ea1.log) directly
  pinned and separately inventoried. Both original stage certificates and all
  certificate regressions pass with the bounded checking pieces. The full Action
  source scans remain in progress.
- [x] Run the full `lake build --wfail` before declaring an extension complete.
  The byte-cache cost milestone passes locally with 4,428
  jobs; all 891 modules were covered by the default targets. The application
  extraction and completeness checkpoint passes 4,465 jobs with all 928 modules
  covered, 32 new declarations directly pinned, and 14 source-certificate
  regressions checked. Its [validation record](review/validation-b3b22e26.log)
  identifies the exact proof baseline. Future theorem commits require their own
  validation; these local results do not assert hosted
  CI success.

Next implementation work: witness construction and runtime refinements. Update the review packet
when its proof baseline changes. Completed theorems remain usable with their current
assumptions throughout.
