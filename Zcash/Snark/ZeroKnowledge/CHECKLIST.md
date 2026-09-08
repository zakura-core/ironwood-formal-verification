# ZK checklist and optional extensions

The interactive statistical HVZK theorem is complete for the circuit relation and
random-tape experiment in [ActionCompilerSimulation.lean](ActionCompilerSimulation.lean).
Valid witnesses, the specified setup, and independent uniform random-bit tapes
can remain assumptions of that theorem. The next phase pursues the instantiations
and additional experiments below, without reopening the completed interactive
target. They remain extensions of that target rather than prerequisites for it.

Checked items have the cited proof or validation evidence. Unchecked items are
future work; adding this checklist does not prove them.

| Optional work | What it adds |
| --- | --- |
| Witness and setup corollaries | Applications of the same theorem to a named relation, witness construction, or parameter set. Validity remains a premise. |
| PRNG instantiation | A computational security reduction under a PRNG assumption, with its distinguishing loss recorded separately. |
| Unlimited independent retries | An explicit unlimited-run distribution built from the finite-budget comparisons and vanishing exhaustion tails. |
| Fiat–Shamir ZK | A noninteractive security theorem with oracle access and a stated hash model. |

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
- [ ] For an application-level `ActionSpec` corollary, define the conversion from
  the private Action witness to the original advice rows. Prove that the specified
  valid witness construction supplies all gate, lookup, and copy premises, recording
  any construction preconditions. Start from
  [ActionSpec](../../Circuits/Action/Spec.lean) and the existing circuit integration.

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
- [ ] Connect that reduction to a stated computational PRNG security definition,
  including its seed-independence, auxiliary-input, and resource conditions.
- [ ] Account for generator state and all replaced tapes in retry extensions,
  including the truncation tail or total randomness budget.

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
- [ ] Define real and simulated noninteractive experiments with a classical,
  query-bounded random-oracle adversary. Specify statement selection, auxiliary
  input, proof count, and oracle access before and after observing the proof.
- [ ] Connect the reference message sequence to
  [the verifier's Fiat–Shamir schedule](../Verifier/FiatShamir.lean), including the
  verifying-key representation, public-instance prefix, domain separators, canonical
  point/scalar encoding, squeeze order, and digest-to-field conversion.
- [ ] Apply the cached-oracle programming theorem to the witness-free Action
  simulator and actual challenge schedule. Prove the required transcript entropy
  and bound prior-query conflicts and other programming failures at every stage.
- [ ] Compose with the joint PLONK and IPA simulation and exceptional-event bounds.
  Prove an explicit final error as a function of Action count and oracle-query
  budget, accounting for wide reduction without charging the same hybrid twice.
- [ ] State the resulting ZK theorem for the proof and the adversary's oracle view,
  with the simulator's resource bound and all model assumptions exposed. Relating
  concrete BLAKE2b to the random oracle remains a cryptographic modeling assumption.
- [ ] If this theorem includes retries, model the shared oracle state across them
  and reprove the retry comparison in that experiment. The independent verifier
  tapes of the interactive retry theorem do not supply this connection.

Closure: a random-oracle ZK theorem with its own simulator and quantified error.
The interactive HVZK theorem and its causality proof are inputs to this work;
they do not by themselves prove Fiat–Shamir ZK.

**Validation and review if an extension is pursued**

- [x] Build changed modules and their dependent trust boundaries; run the required
  endpoint and axiom checks. Pin every new logical declaration, including helpers
  outside the endpoint-name census. All completed milestones have these checks.
  The cached-oracle milestone adds 31 direct pins and passes the 283-endpoint census.
- [x] Run the full `lake build --wfail` before declaring an extension complete.
  The cached-oracle milestone passes locally with 4,208 jobs, and all 768 modules
  are covered by the default targets. Future theorem commits require their own
  validation; these local results do not assert hosted CI success.
- [ ] Review the final theorem statement, simulation experiment, and transitive
  assumptions against the claim. Obtain independent review before describing the
  extensions as independently audited.

If these extensions are pursued, a useful order is relation/setup corollaries,
the randomness interface, unlimited interactive retries, and Fiat–Shamir simulation,
followed by any combined PRNG and retry corollaries. The completed interactive
theorem remains usable with its current assumptions throughout.
