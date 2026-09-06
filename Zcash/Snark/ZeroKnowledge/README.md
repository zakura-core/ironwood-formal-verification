# Zero-knowledge formalization

This development starts from the [pinned prover description](https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md),
on Ironwood base `ad4a6ad8f75a64368bae4186006480410a687cce`. The description names Sensei
`56a7de7`; that implementation commit has not yet been located. These are proofs about the
specified constructions, not a verified correspondence with that Rust executable.

There is not yet a zero-knowledge theorem for the complete prover. The existing verifier and
soundness formalization does not supply an honest-prover distribution or simulator.

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
These component bounds alone do not establish a joint transcript law. The IPA law is covered
below; the earlier PLONK view remains a separate obligation.

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

The result retains correlations within this projection. Connecting its additive offset and
query ordering to the complete multi-opening construction, and simulating the other PLONK
messages, remain open. The theorem has supplied distinct evaluation points and does not
condition on a Fiat–Shamir execution's observed challenges.

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

These results do not establish the preceding PLONK/multi-opening simulation,
Fiat–Shamir zero-knowledge, a verified concrete PRNG, or correspondence with the Rust
prover. Identifying the final verifier equation does not discharge those gaps.

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

These column results do not establish the adaptive construction of all lookup/permutation
polynomials, the full multi-opening simulation, or the actual challenge-generation law.

## Checks

`lake build Zcash.Snark.ZeroKnowledge.TrustBoundary` checks the proofs and their transitive
axiom dependencies. The sampling program is also pinned as computable. This directory is
included in the default library build, and its trust boundary is imported by `CensusCheck`.
