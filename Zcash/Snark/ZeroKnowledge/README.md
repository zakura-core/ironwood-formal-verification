# Zero-knowledge formalization

This development starts from the [pinned prover description](https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md),
on Ironwood base `ad4a6ad8f75a64368bae4186006480410a687cce`. The description names Sensei
`56a7de7`; that implementation commit has not yet been located. These are proofs about the
specified constructions, not a verified correspondence with that Rust executable.

There is not yet a zero-knowledge theorem for the complete prover. The existing verifier and
soundness formalization does not supply an honest-prover distribution or simulator.

The implementation-facing interactive target is **statistical HVZK**. The
[Halo2 book's perfect SHVZK model](https://zcash.github.io/halo2/design/protocol.html)
restricts the verifier's challenge space, including excluding zero and evaluation-domain
points. The pinned implementation does not enforce all those exclusions. Exact conditional
simulation of a component is therefore not a perfect SHVZK theorem for this prover. Neither
the nonuniform sampler nor an upper bound on simulation error alone disproves perfect ZK.

## Field sampling

[Randomness.lean](Randomness.lean) models an independent uniform 512-bit integer reduced
modulo the Vesta scalar-field order `p`. No hash is applied in this sampler. It reuses the
existing `challenge255` arithmetic calculation; that reuse does not assume that a concrete
PRNG supplies independent uniform words or that BLAKE2b is a random oracle.

Writing `2^512 = Qp + r`, each residue below `r` has `Q+1` preimages and each remaining
residue has `Q`. The law is provably different from a uniform field sample. Its exact
reduction bias is `r(p-r)/(p·2^512)`, bounded by `2^-260`. Nonuniform masks alone neither
prove nor refute zero-knowledge of the joint proof distribution.

[Sampling.lean](Sampling.lean) proves both directions of the event-probability comparison
after any deterministic computation on `N` such samples, with bound `N × bias`. The
continuation can return errors and can perform hashing and serialization; the theorem does
not condition on success. The description's declared count is `148m + 46` field samples
for `m` Actions, or 1,552 / 2,736 64-bit words for one / two Actions. Instantiating the
continuation with a fully modeled prover and verifying that count against Rust remain open.

## Masking optimizations

The two constructions follow these pinned Common changes:

| Change | Source merge | Checked result |
| --- | --- | --- |
| [#225: power-of-two IPA support](https://github.com/zakura-core/common/pull/225) | `b811257a0cedad053cedb6b3bf531107f8561b2a` | The complete folded scalar is uniform or publicly zero under ideal field masks, for `ξ ≠ 0`. |
| [#267: linear evaluation mask](https://github.com/zakura-core/common/pull/267) | `b2f9ab127f9b5034697bbd15557c24b37e035fa4` | For `q ≠ x`, the pair `(r(x), offset(r(x)) + r(q))` is uniform under ideal field coefficients. |

[IpaFold.lean](IpaFold.lean) derives the coefficient functional from the recursive update
`a := a_lo + u⁻¹ a_hi`. [SparseIpa.lean](SparseIpa.lean) applies it to
`s(X) = Σ_t α_t(X^(2^t) − q^(2^t))`. If any direction differs from evaluation at `q`,
the scalar has a nonzero mask coefficient. If every direction agrees, the **entire fold**
equals evaluation, and the valid opening vector `P + ξs − P(q)` gives `c = 0`. The latter
case is simulatable; it is not a witness-dependent rank failure.

[LinearMask.lean](LinearMask.lean) proves the two-evaluation bijection and its inverse.
Appending `r` last in a Horner fold gives it coefficient one, including when the batching
challenge is zero. [MaskPolynomials.lean](MaskPolynomials.lean) relates both constructions
to the existing computable polynomial representation.

[MaskSampling.lean](MaskSampling.lean) transfers these component results to the implemented
field law: the sparse scalar costs at most `k × bias`, and the linear-mask pair at most
`2 × bias`, in either direction. These are laws with **supplied public challenges**;
they do not describe a Fiat–Shamir execution conditioned on its observed challenges.
These component bounds alone do not establish a joint transcript law. The joint algebraic
simulation below composes them with the pre-IPA messages under explicit quotient and
challenge premises; a full execution including failures remains a separate obligation.

## Linear mask with its commitments

[LinearMaskTranscript.lean](LinearMaskTranscript.lean) extends the Common #267 result to a
four-field projection: `R`, `r(x)`, the commitment to `Q'`, and the later masked group
evaluation. The unblinded `Q'` commitment may depend on both coefficients of `r`. The additive
offset in the later evaluation may depend on the disclosed `r(x)`.

[CommitmentMask.lean](CommitmentMask.lean) proves that independent uniform commitment blinds
make a whole family of points jointly uniform and independent of separately disclosed data.
Combining that fact with the two-evaluation bijection proves the four-field simulation law.
The implemented field law gives the two-sided bound **4 × bias**, accounting for the two
coefficients and two commitment blinds. These are four selected draws; other draws intervene
between them in the complete prover. A computable simulator uses four field coins and `W`.

The result retains correlations within this projection. The pre-IPA development below
connects the additive offset to the pinned opening groups and includes the other scalar
messages. The multi-opening construction below supplies valid IPA input from actual group
evaluations; its connection to the full emitted transcript remains open. These theorems
have supplied distinct evaluation points; they do not condition on a Fiat–Shamir
execution's observed challenges.

## Joint IPA simulation

`idealIpa_simulation_capstone` in [IpaSimulation.lean](IpaSimulation.lean) proves exact
equality between the honest and simulated **algebraic IPA transcript** for ideal independent
field masks and blinds. The transcript includes `S`, every `L/R`, `c`, and `f`. It quantifies
over every valid opening of the same public commitment and evaluation, with `ξ ≠ 0`, nonzero
round challenges, and a group generated by `W`. The last condition follows from `W ≠ 0`
and equality of the group and scalar-field cardinalities; the deployment must supply these
facts for its actual parameters.

[IpaProver.lean](IpaProver.lean) computes the cross terms and proves their recursive
equation. [IpaTranscript.lean](IpaTranscript.lean) adds the sparse mask and every independent
blind, proving the final equation with the **computed** `f`. The simulation proof changes
variables from the private blinds to jointly uniform round messages and `f`; the mask
commitment is then determined by that equation. This removes the witnesses from the entire
IPA view, including its correlations.

[IpaSimulator.lean](IpaSimulator.lean) implements the simulator from public data and field
coins. It samples group points as multiples of `W` and solves for `S` using `ξ⁻¹`. The
discrete-log inverse used in the distribution proof does not occur in this algorithm.

[IpaSampling.lean](IpaSampling.lean) models the ordered tape: `k` mask coefficients, one
mask-commitment blind, then `k` left/right pairs. It proves the indexing and the `3k+1` count.
`sampledIpa_simulation_error_bound` gives the two-sided bound `(3k+1) × bias` against the
same simulator for the implemented reduction law: **34 × bias at k = 11**.

[IpaVerifier.lean](IpaVerifier.lean) proves that this transcript's equation is equivalent to
zero evaluation of the existing [`ipaFold`](../Verifier/Ipa.lean) MSM. It connects the
recursive folds to `computeS` and `computeB`, and extracts the IPA fields from `ProofString`
to establish the same correspondence inside `assembleFinalMsm`.

## Fresh IPA challenges and failed attempts

[IpaChallenges.lean](IpaChallenges.lean) supplies the verifier's independent tape in order:
`ξ`, `z`, then the `k` round challenges. [IpaFresh.lean](IpaFresh.lean) retains that tape in
the joint view and removes the nonzero-challenge premises by charging the probability that
`ξ` or a round challenge is zero. No exclusion on `z` is needed. Zero `ξ` is included even
though the specified implementation does not automatically retry it.

For independent wide-reduced verifier coins and wide-reduced prover masks, the two-sided
event bound is `(k+1)/p + (4k+3) × bias`: **12/p + 47 × bias at k = 11**. It covers the
complete challenge/transcript pair, for every valid opening of the given public commitment.
This is a statistical comparison of interactive experiments. It does not assume that
Fiat–Shamir challenges are independent after conditioning on a proof transcript.

[IpaAttempt.lean](IpaAttempt.lean) transports the bound through an explicit attempt observer.
It writes `S`, receives `ξ,z`, then writes each `L` and `R` before receiving its round
challenge. A failed point encoding stops before that point contributes bytes; a zero round
challenge requests fresh randomness after both point writes. The observer retains the
emitted prefix, received challenges, status, and the verifier's entire tape, including
unused coins. The final scalars appear only after the rounds complete.

The codecs are parameters; the theorem does not certify a Rust encoder. Its law is
unconditioned and includes failed attempts. The following result handles normalization
and independent retries of this IPA experiment.

## Successful IPA attempts and independent retries

[IpaPoints.lean](IpaPoints.lean) proves that all `2k+1` honest emitted points are jointly
uniform under ideal commitment blinds, even at exceptional challenges. This is a point
projection used to bound failures; the separate joint transcript theorem also retains
`c` and `f`. [IpaFailures.lean](IpaFailures.lean) proves the exact success criterion when
the point codec fails precisely on the identity: every point is nonidentity and every
round challenge is nonzero. The honest wide-reduced attempt's failure probability is at
most **34/p + 47 × bias** for eleven rounds.

[Conditioning.lean](Conditioning.lean) accounts for the change in normalizers when both
experiments discard failures. [IpaRetry.lean](IpaRetry.lean) proves that the honest and
simulated success probabilities are positive for eleven rounds. Its
`wideSuccessfulIpa_simulation_capstone` compares the complete successful encoded view,
including the verifier tape, with a simulator that has no witness or commitment-blind
argument. Writing `ε = 12/p + 47 × bias` and `B = 46/p + 94 × bias`, the two-sided bound
is **2ε/(1−B)**. The kernel checks `B < 1`; success is not an assumed premise.

[Retry.lean](Retry.lean) models independent fresh attempts with a finite budget. If one
attempt fails with probability `f`, exhausting `N` attempts has exactly probability
`f^N`; every event converges to its probability under the successful-attempt law.
The IPA result uses the same fixed public opening on each attempt. A full prover that
restarts PLONK too, carries state between retries, or exposes failed attempts requires
its corresponding full execution model.

These IPA results start from a valid public opening. The joint algebraic construction below
derives that opening under explicit quotient-correctness premises and supplied challenges.
Handling failures across the full computation, Fiat–Shamir zero-knowledge, a verified
concrete PRNG, and correspondence with the Rust prover remain open. Identifying the final
verifier equation does not discharge those gaps.

## Replacement-row masks

[RowMaskRank.lean](RowMaskRank.lean) proves joint uniformity of the evaluations of the
existing `rowPolynomial` interpolation. With `n - firstMasked` random suffix values, any
family of at most that many distinct observation points is hidden, provided it avoids the
unmasked domain rows. The proof constructs an interpolating polynomial with arbitrary
observation values and zeros at every unmasked row, establishing surjectivity of the whole
evaluation map. [LinearImage.lean](LinearImage.lean) then proves uniformity through a kernel
fiber equivalence.

[RowMaskSampling.lean](RowMaskSampling.lean) verifies the increasing-row tape order and
transfers that law to the wide-reduced sampler. The pinned advice size has six replacement
rows; permutation/lookup product polynomials have five. [RowMaskTranscript.lean](RowMaskTranscript.lean)
includes the coefficient commitment and its independent blind in the same joint view.
The sampling bounds are **7 × bias** for a six-row column with its commitment and **6 × bias**
for a five-row column with its commitment.

[DomainCertificate.lean](DomainCertificate.lean) proves the existing root literal's order
using binary modular exponentiation checked by Lean's kernel. The concrete 2048-row facts
therefore do not depend on CompElliptic's native parameter certificate.

At an unmasked domain point the polynomial instead reveals the original witness cell,
for every mask. [Observation.lean](Observation.lean) proves the resulting difference between
the joint challenge/evaluation views of different row vectors, including under the
wide-reduction challenge law. This is a column-view result: an end-to-end impossibility
claim still requires two satisfying witnesses for the same public statement and a proof
that the full execution exposes the observation after accounting for aborts and retries.

## Joint columns and pre-IPA messages

[ColumnSequence.lean](ColumnSequence.lean) extends the column result to a sequence of
retained-row constructors that may read **all earlier private masked rows**. The induction
removes the future view for each private history, so it does not assume independence merely
from earlier disclosed evaluations. [PlonkColumns.lean](PlonkColumns.lean) installs the
ten advice, six lookup-permutation, and six product columns per Action, including their
six-row and five-row suffix sizes.

[PreIpaMask.lean](PreIpaMask.lean) jointly simulates all pre-IPA commitments, five common
evaluations of every private column, `r(x)`, and the masked `Q₀(q)`. The unblinded commitment
cores may depend on all private rows and both coefficients of `r`. Independent commitment
blinds hide them jointly with the scalars. Under ideal field samples, the view has an exact
public simulator law when the observation points are distinct, off the row domain, and
`q ≠ x`.

[ColumnTape.lean](ColumnTape.lean) first proves a canonical interleaved representation.
[BatchedTape.lean](BatchedTape.lean) and [PlonkTape.lean](PlonkTape.lean) then convert the
actual batch layout observed in the available Bento checkout
`e32e61eb35b6e5b5e0600cb0903adcfe0cd617d8`, at
`crates/sensei/src/native/randomness.rs`: ten advice tails before their ten blinds per
Action; both lookup tails before their two blinds; singleton product batches. Each
equivalence preserves the tail and blind subsequences. This establishes the model's
`148m` private-column draws and `148m + 12` pre-IPA draws; adding the IPA's 34 gives
`148m + 46`. The available checkout is distinct from the unlocated `56a7de7` pin, and these
equivalences are not a proof of Rust execution correspondence.

[PlonkOpening.lean](PlonkOpening.lean) constructs the pinned five opening-polynomial groups
and their Horner folds. It proves that `Q₀(q)` is precisely the first group's weighted
prefix plus `r(q)` at coefficient one, even for zero `x₁`. Each remaining group value is a
fold of the column evaluations at `q`. The collapsed quotient `H_x` may depend on every
private row; its value at `q` remains hidden inside `Q₀(q)`.

[PlonkTranscript.lean](PlonkTranscript.lean) computes the emitted step-5 scalar sequence and
the five step-6 group evaluations from those polynomials, and proves that together with the
commitments they are a public projection of the joint mask view. The simulator receives
only public polynomials and challenges. For the batched wide-reduction sampler, the entire
algebraic pre-IPA message view has two-sided event error at most
**`(148m + 12) × bias`**, with supplied distinct points
`x, xω, xω⁻¹, xω⁻⁶, q` outside the 2048-row domain.

That hiding result quantifies over supplied retained-row algorithms, quotient pieces, and
unblinded commitment cores. The joint construction below instantiates the cores and
composes with the IPA. The row and quotient algorithms, their constraint correspondence,
early failures, and the actual challenge law still require integration. These results do
not condition a Fiat–Shamir execution on its challenges or establish whole-prover HVZK.

## Computed multi-opening and IPA input

[MultiopenPolynomial.lean](MultiopenPolynomial.lean) computes each group's interpolant,
vanishing polynomial, and quotient `(Q_i − R_i) / V_i`. For actual evaluations at distinct
nodes, it proves exact divisibility and that the folded `Q'` evaluates to the scalar
reconstructed by the existing `multiopenEval` verifier routine when `q` avoids those nodes.

[PolynomialCommitment.lean](PolynomialCommitment.lean) connects the coefficient-vector
commitment to both polynomial and blind folds. [MultiopenIpa.lean](MultiopenIpa.lean) uses
those identities to derive both valid-opening premises of the IPA theorem: the existing
`multiopenCombine` commitment opens to the computed `P` with the actually folded `ρ_P`,
and its reconstructed value equals `P(q)`. Degree bounds prove that converting `P` to an
IPA vector does not truncate any coefficients.

[PlonkMultiopen.lean](PlonkMultiopen.lean) instantiates this with the exact five pinned
groups and their point sets. It includes blind one for public instance, fixed, and `σ`
polynomials, the weighted sum of the eight quotient-piece blinds in `H_x`, and each
private column's blind. Private-row polynomials and the linear mask satisfy the degree
bound by construction; bounds on the supplied public polynomials and quotient pieces
remain explicit premises.

The resulting IPA transcript has an exact ideal simulation and a two-sided
**`34 × bias`** bound with wide-reduced IPA coins, for nonzero `ξ` and round challenges.
These results hold for every preceding private state and do not assume that the incoming
blind is independent of earlier messages. They still start from the resulting public IPA
opening. The next construction rebuilds it from the public mask view, assuming agreement
of the inferred `H_x(x)` with the honest quotient. The verifier-typed construction below
instantiates the constraint function; full proof-string routing remains open. The available
Rust implementation's repeated synthetic division has not yet been related formally to
this quotient computation.

## Joint algebraic prover simulation

[PlonkCommitments.lean](PlonkCommitments.lean) instantiates every pre-IPA commitment core
with its actual coefficient polynomial: the private row columns, linear mask, eight
quotient pieces, and computed `Q'`. It reads their blinds from the same commitment positions.
The polynomial-only `Q'` construction is independent of every commitment blind.

[PlonkPublicOpening.lean](PlonkPublicOpening.lean) reconstructs the five group commitments
and all their node evaluations from the enriched public view. It proves that applying the
existing `multiopenEval` and `multiopenCombine` operations gives the honest IPA input.
The inferred `H_x(x)` comes from a supplied public function `expectedHx`. Agreement of that
function with the honest quotient is an explicit premise. The construction below
instantiates it with the verifier's actual constraint calculation.

`idealPlonkJoint_simulation_capstone` in [PlonkComposition.lean](PlonkComposition.lean)
proves exact equality of the **joint pre-IPA view and complete IPA transcript** with one
public simulator under ideal field samples. The proof first simulates the IPA for each
reachable private state, then replaces the preceding public-view distribution. It retains
the actual dependence of the IPA polynomial and blind on all earlier private coins.
Degree bounds and quotient agreement are required only for row states in the honest
construction's support. They are not yet derived from an Orchard witness relation.

[PlonkSampling.lean](PlonkSampling.lean) connects this joint computation to the batched
pre-IPA tape and ordered IPA suffix. All `148m + 46` field draws feed one deterministic
prover computation. `sampledPlonkJoint_simulation_error_bound` gives the two-sided event
bound **`(148m + 46) × bias`** against the same simulator. Its premises remain: a blinding
generator spanning the group; the quotient and degree obligations above; nonzero `ξ` and
IPA round challenges; and five distinct observation points outside the 2048-row domain.
The challenges are supplied inputs, not a conditioned Fiat–Shamir transcript.

[PlonkSimulator.lean](PlonkSimulator.lean) implements the joint simulator from field coins.
It samples points as multiples of `W`, samples the column observations directly, rebuilds
the public IPA input, and runs the existing IPA simulator. Its field-coin law is proved
equal to the simulator used by the joint theorem. No witness, private row or quotient
constructor, or discrete-log inverse appears in this algorithm.

## Computed quotient and verifier-typed proof

[PlonkProofString.lean](PlonkProofString.lean) projects the joint view into the existing
`ProofString` at the captured Orchard dimensions. Its `plonkVerifierHx` calls the existing
`allExpressions` and `expectedHEval` functions. It proves that this public calculation
is exactly the quotient value inferred from the projected proof. The calculation reads
only the public key, statement polynomials, challenges, and column claims.

[PlonkConstraints.lean](PlonkConstraints.lean) constructs the gate, permutation, and lookup
numerator from the actual rotated row polynomials and canonical Lagrange selectors.
`plonkConstraintNumerator_eval` proves that its evaluation is the verifier's precise
constraint fold. [QuotientPieces.lean](QuotientPieces.lean) computes polynomial division by
`X^2048 - 1` and cuts eight consecutive coefficient blocks. Recombination, per-piece degree
bounds, and quotient agreement are proved from divisibility and numerator capacity.

`sampledPlonkVerifier_simulation_error_bound` in
[PlonkQuotientSimulation.lean](PlonkQuotientSimulation.lean) uses these computations to
simulate the **complete algebraic `ProofString`**, with the same two-sided
**`(148m + 46) × bias`** bound. An arbitrary quotient constructor and arbitrary inferred-value
callback are no longer inputs. Instead, each reachable honest row state must produce a
numerator divisible by `X^2048 - 1` and of degree below `9 × 2048`; public polynomial degree
bounds and the earlier challenge/generator conditions remain explicit. The next result
derives the capacity requirement from public circuit syntax.

[LookupDegree.lean](LookupDegree.lean) keeps the lookup input and table degree bounds
separate. [PlonkDegree.lean](PlonkDegree.lean) then proves the full numerator has degree at
most `9 × 2047`, for every row state, from a public profile: gate degree at most nine,
permutation chunks of at most seven columns, lookup input degree at most four, and table
degree at most one. [PlonkDegreeCertificate.lean](PlonkDegreeCertificate.lean) kernel-checks
that profile for both captured keys without using their earlier native certificates.

`sampledPlonkVerifier_capacity_simulation_error_bound` in
[PlonkCapacitySimulation.lean](PlonkCapacitySimulation.lean) supplies that derived capacity
to the complete algebraic proof simulation. Divisibility of the constraint numerator on
each reachable row state remains the only private-state premise. The public polynomial,
generator, and supplied-challenge conditions still apply.

[DomainDivisibility.lean](DomainDivisibility.lean) proves that vanishing on every domain
row is equivalent to divisibility by `X^n - 1`. It applies this to the actual constraint
fold. `sampledPlonkVerifier_rows_simulation_error_bound` in
[PlonkRowSimulation.lean](PlonkRowSimulation.lean) therefore derives both quotient
premises from public degree bounds and row-wise satisfaction of the gate, permutation,
and lookup constraints. Correctness of the lookup sorting and product-row constructors
has not yet supplied that satisfaction premise. Satisfying advice columns are inputs
in the pinned protocol; generating the underlying circuit witness is outside its scope.

[ExceptionalMixtures.lean](ExceptionalMixtures.lean) and
[PlonkExceptional.lean](PlonkExceptional.lean) remove the requirement that every random
row state has a valid quotient. They retain the probability of exceptional private states
under the ideal row law and add it to the complete sampling bound. The comparison uses
the original, unconditioned row distribution and the inherited IPA blind.

`sampledPlonkVerifier_consistency_error_bound` in
[PlonkConsistency.lean](PlonkConsistency.lean) applies this to the computed numerator and
existing proof type. Its bound is **`invalidRowMass + (148m + 46) × bias`**. The first term
is the ideal probability that `X^2048 - 1` does not divide the actual numerator. The
theorem no longer assumes row correctness; a separate result bounds that term by the
probability of any violated row constraint. Bounding it numerically for the actual lookup
and product algorithms, including zero denominators, remains necessary. Public polynomial,
degree-profile, generator, and supplied-challenge premises still apply.

[PlonkChallenges.lean](PlonkChallenges.lean) records all `11 + k` verifier challenges in
their squeeze order and defines both uniform and wide-reduced independent tape laws.
Replacing this tape's field samples costs at most `(11 + k) × bias`.
`freshPlonkVerifier_simulation_error_bound` in [PlonkFresh.lean](PlonkFresh.lean) retains
the complete challenge tape alongside the existing `ProofString`. Its bound is:

**`badChallengeMass + averageInvalidRowMass + (148m + 46) × bias`**.

This result no longer assumes a good fixed challenge tape or correctness on every private
row state. It samples the original challenge law without rejecting exceptional values,
and averages row inconsistency over that law. The simulator uses only the public input
and the same challenge law. Independent verifier coins do not establish Fiat–Shamir
zero-knowledge.

[PlonkChallengePoints.lean](PlonkChallengePoints.lean) and
[PlonkChallengeBounds.lean](PlonkChallengeBounds.lean) bound the public exceptional event
by **`(k + 4102)/p`** for uniform coins, plus **`(k + 11) × bias`** for wide reduction.
This counts `x = 0`, `xi = 0`, the `k` zero folding challenges, two size-2048 domain-hit
events, and four collisions between the later point and a rotated first point.
At `k = 11`, `wideFreshPlonkVerifier_simulation_error_bound` in
[PlonkFreshBounds.lean](PlonkFreshBounds.lean) gives:

**`averageInvalidRowMass + 4113/p + (148m + 68) × bias`**.

The row term averages the ideal private row law over the wide-reduced verifier law.
Bounding it for the actual lookup and product constructors and relating the offline
tape experiment to the actual interactive schedule remain open.

This is still a conditional algebraic simulation theorem. Completing the exact prover
theorem requires the actual row algorithms and their correctness, the full verifier's
grouping and commitment routing, failures and retries across the whole prover, the challenge
model and Fiat–Shamir argument, and correspondence with the Rust implementation. The
available Rust quotient implementations have not been proved equivalent to these polynomial
computations, and byte encoding is outside the typed proof result.

## Checks

`lake build Zcash.Snark.ZeroKnowledge.TrustBoundary` checks the proofs and their transitive
axiom dependencies. The sampling program is also pinned as computable. This directory is
included in the default library build, and its trust boundary is imported by `CensusCheck`.
