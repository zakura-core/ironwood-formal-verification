# ZK checklist and optional extensions

The interactive statistical HVZK theorem is complete for the circuit relation and
random-tape experiment in [ActionCompilerSimulation.lean](ActionCompilerSimulation.lean).
Valid witnesses, the specified setup, and independent uniform random-bit tapes
can remain assumptions of that theorem. The next phase pursues the instantiations
and additional experiments below, without reopening the completed interactive
target. They remain extensions of that target rather than prerequisites for it.
The one-attempt programmable-random-oracle distribution theorem is also complete,
including its fixed-bit simulator. The remaining work concerns witness construction,
PRNG security and state, shared-oracle retries, simulator runtime, and independent
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
- [ ] Specify the inputs and preconditions of an application-level witness
  constructor, starting from [ActionSpec](../../Circuits/Action/Spec.lean).
  Separate witness-generation correctness from the already proved circuit-level
  ZK statement; do not assume successful proof emission or verifier acceptance.
- [ ] Define the conversion from a valid private Action witness to original advice
  rows, including the actual region placement and public-input layout.
- [ ] Prove that the constructed rows satisfy every original gate, lookup tuple,
  and compiler copy equation, recording any additional construction preconditions.
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
- [ ] Define the computational PRNG security game, including the admissible
  distinguisher class or concrete resource budget. Sample the seed independently
  of retained auxiliary data and make the generated output length explicit.
- [ ] Instantiate that game with the existing Action reduction. Prove equality of
  the actual distinguishing experiments and expose the required resource-class
  membership; connect that membership to the runtime work below.
- [ ] Define continuous generator state across attempts and its finite tape
  allocation policy. Prove that replay uses the same state evolution rather than
  silently reseeding, and state whether unused attempt words are discarded.
- [ ] Prove the finite-retry computational comparison for every replaced tape,
  retaining all observed failures and accounting for the total randomness budget.
- [ ] If extending a computational claim to unlimited retries, include a checked
  truncation argument and its exhaustion tail under the stated execution model.

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
- [ ] Define finite retained-history retries with a shared oracle cache, fresh
  private randomness per attempt, and a fixed statement and witness. Retry only
  `retryRandomness`; completion, terminal opening errors, and simulator programming
  failure stop. Keep all preceding observed failures and the final cache.
- [ ] Prove the shared-cache transition and history laws, including the cache
  budget through every attempted proof. Preserve adaptive preprocessing and
  postprocessing in the same oracle experiment.
- [ ] Derive the two-sided statistical comparison for every finite attempt budget,
  including prior-query conflicts, internal retry-cache growth, simulator sampling
  bias, and explicit exhaustion.
- [ ] For an unlimited shared-oracle extension, define its complete observation
  space and handle possible nontermination. Establish the needed tail or limiting
  theorem in that model; the independent-tape termination theorem cannot supply it.

Closure for one attempt: the classical programmable-random-oracle distribution
theorem, its computable simulators, and their sampling/query budgets are checked,
including a simulator driven by a fixed uniform bit tape.
The interactive HVZK theorem and its causality proof are inputs to this separate
oracle argument. Shared-oracle retries and bit-level runtime analysis extend its scope.

**6. Simulator runtime: connect resource counts to execution cost**

- [x] Provide a computable simulator with a fixed uniform bit-input length and
  checked oracle-cache bounds in [ActionOracleBits.lean](ActionOracleBits.lean).
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
- [ ] Use the checked runtime bound to discharge the PRNG reduction's resource
  conditions wherever that computational instantiation is claimed.

Closure: a bound on the same simulator's execution cost follows from a specified
cost model and explicit primitive assumptions. Computability and a fixed random
tape alone do not prove that running-time statement.

**7. Review: prepare the evidence and obtain independent assessment**

- [ ] Prepare a review packet mapping each advertised claim to its exact theorem,
  real/simulated experiment, validity/setup/randomness assumptions, error formula,
  failure policy, and runtime scope. Include the checked commit and validation log.
- [ ] Check that theorem inputs and public observations match the intended claim,
  including auxiliary data, retained prefixes, oracle state, and exhaustion.
- [ ] Recheck transitive dependencies and every new declaration pin at the review
  commit, with no admitted lemma or new unlisted native certificate.
- [ ] Obtain independent review of the packet and record the reviewed commit,
  findings, resolutions, and remaining qualifications. A local self-review or
  passing Lean build does not complete this item.

**Validation and review if an extension is pursued**

- [x] Build changed modules and their dependent trust boundaries; run the required
  endpoint and axiom checks. Pin every new logical declaration, including helpers
  outside the endpoint-name census. All completed milestones have these checks.
  The fixed-bit simulator milestone adds 39 direct pins and passes the
  297-endpoint census. Its concrete declarations retain only the two existing
  Pasta curve-order native certificates.
- [x] Run the full `lake build --wfail` before declaring an extension complete.
  The fixed-bit simulator milestone passes locally with 4,234 jobs, and all 794 modules
  are covered by the default targets. Future theorem commits require their own
  validation; these local results do not assert hosted CI success.

Next implementation order: finite shared-oracle retries, the computational PRNG
security interface and finite generator-state replay, witness-construction and
runtime refinements, then any unlimited shared-oracle or computational retry
extension. Prepare the review packet as those statements stabilize. Completed
theorems remain usable with their current assumptions throughout.
