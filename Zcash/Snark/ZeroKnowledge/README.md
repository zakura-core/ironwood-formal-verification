# Zakura 1.4.0 zero knowledge

This directory contains Lean proofs of both:

- **Statistical honest-verifier zero knowledge (HVZK)** for the interactive protocol.
- **Statistical zero knowledge (ZK)** for its Fiat–Shamir transform in the
  **classical programmable random-oracle model**.

The proofs compare the verifier's view with a simulator that receives no private
witness. The release target is one post-NU6.3 Orchard proof call in Zakura 1.4.0,
using Common `50f712ee22ca95e2dd5230c6f331ce2e433d70ee`, with `k = 11` and
2,048 rows. The [release provenance](Zakura/PROVENANCE.md) pins the sources,
published crates, feature profiles, and implementation boundary. The
[prover description][protocol] supplies the reference masking equations.

The release model returns proof bytes, returns an error, or records the zero-IPA
panic. It has no retry-request status, resampling step, or automatic retry.
Public identity commitments fail before the first prover oracle query. The
IPA receives the actual polynomial evaluation on an opening-node collision,
matching the released algebraic fallback within the same call. The
release observation and its theorem connection require Lean elaboration;
source and artifact checks alone do not validate the new proof terms.

[Results](#main-results) · [Bounds](#error-bounds) ·
[Assumptions](#assumptions-and-scope) · [Build](#build-and-reference)

## Main results

| Result | Start here |
| --- | --- |
| **Interactive HVZK:** statistical comparison of the complete observed attempt, including failed prefixes. | [ActionInstantiation.lean](ActionInstantiation.lean) |
| **Fiat–Shamir ZK:** statistical comparison of the full oracle view, including adaptive queries before and after the attempt. | [ActionFiatShamir.lean](ActionFiatShamir.lean) |
| **Released call observation:** one proof, returned error, or panic, with the oracle cache retained. | [Zakura/Action.lean](Zakura/Action.lean) |
| **Action connection:** construct circuit rows from application witnesses and prove their validity. | [ActionWitnessSimulation.lean](ActionWitnessSimulation.lean) |
| **Prover completeness (awaiting final build):** bound abort or rejection from valid application witnesses, including an initialized call with a fresh random oracle. | [Interactive](ActionProverCompleteness.lean), [initialized call](Zakura/Completeness.lean) |
| **Executable simulator:** a fixed-bit implementation with a proved distribution and structural resource bounds. | [ActionOracleBits.lean](ActionOracleBits.lean), [program model](PROGRAMS.md) |
| **PRNG reduction:** a computational interactive simulation bound under an explicit generator-security assumption. | [CostedInteractivePrng.lean](CostedInteractivePrng.lean) |

Both masking optimizations, the sparse IPA mask and linear multi-opening mask,
are covered jointly with PLONK. The linked theorem statements give the exact
experiments and premises.

## Error bounds

For `m ≥ 1` Actions, let `p` be the scalar-field order and `δ` the statistical
distance of one uniform 512-bit integer reduced modulo `p` from a uniform field
element. The one-attempt interactive bound is:

```text
δ = r(p − r)/(p · 2^512) ≤ 2^-260,    where 2^512 = Qp + r
ε(m) = (42882m + 4113)/p + (148m + 70)δ < m · 2^-238
```

**For one Action, the interactive simulation error is below 2⁻²³⁸.**
Any test of the verifier's view has probabilities differing by at most `ε(m)`
between the real prover and simulator.

The one-attempt Fiat–Shamir bound adds `q_pre/p`, where `q_pre` counts prior
oracle queries. The fixed-bit simulator adds a further `(132m + 36)δ`.
The deterministic released-call observation preserves the ideal-field
simulator's `ε(m) + q_pre/p` bound. [PROGRAMS.md](PROGRAMS.md) describes the
PRNG reductions and their assumptions.

A complete private tape contains `148m + 46` field samples; a stopped call
can consume only a prefix. The `148m + 70` coefficient counts sampling-bias
costs in the comparison, not the private tape length.

The new completeness theorem reuses the existing Action circuit completeness
proof. Its proposed bound counts both aborted attempts and completed proofs
rejected by the typed verifier:

```text
η(m) = (42904m + 8271)/p + (296m + 160)δ < m · 2^-238
Pr[completed and accepted] ≥ 1 − η(m),    m ≥ 1
```

This is high-probability completeness for one interactive attempt. The new
[acceptance proof and binary bound](ActionProverCompleteness.lean) await the
requested final Lean build. The [call bridge](Zakura/Completeness.lean) preserves
the same bound for the modeled Fiat–Shamir call with an empty initial oracle
cache and successful public initialization.

## Assumptions and scope

- **Witnesses:** [application construction conditions](ActionWitnessConditions.lean),
  including `ActionSpec`, defined hashes, canonical encodings, and scalar-hint bounds.
  The Action circuit, compiler, masking conditions, commitment routing, and codecs
  are connected by the formalization.
- **Setup:** eleven IPA rounds and a nonidentity blinding generator. The
  [captured-setup corollary](ActionInstantiation.lean) supplies these facts for
  its named setup.
- **Randomness:** fresh, independent uniform raw-bit tapes, with field elements
  sampled by wide reduction. Seeded-generator results instead use the stated
  PRNG security assumption.
- **Invocation:** one call with matching post-NU6.3 circuit/key versions and
  instance counts. Exceptional challenges are not resampled. Failed calls do
  not return the partial proof buffer; oracle queries remain observable.

Fiat–Shamir uses a classical programmable random oracle. Concrete BLAKE2b
security, whole-program Rust equivalence, and machine-instruction timing are
outside these protocol and structural-cost theorems.
The [implementation notes](Zakura/OPTIMIZATIONS.md) record source review of
optimized Rust computation and randomness consumption. The release refresh uses
the existing verifier fixture formats, generated by pinned Rust and checked in
Lean, while retaining the unchanged circuit dumps. New RNG/trace instrumentation
is outside this task. Auxiliary caller-composition theorems
in the library are outside this release claim and are not invoked by its model.

## Build and reference

From the repository root:

```sh
python3 scripts/check_zakura_release.py
lake build --wfail
```

The default build includes this development and its trust census.
The provenance document gives the authenticated source check, existing-fixture
refresh commands, and optional backend regressions. The checked-in verifier
captures were regenerated from the pinned Zakura release and are consumed by
the default fixture checks.

- [PROGRAMS.md](PROGRAMS.md): executable programs and the resource model.
- [Zakura/PROVENANCE.md](Zakura/PROVENANCE.md): exact release target and validation limits.
- [Computability boundary](../../../book/src/formal-verification/zero-knowledge.md):
  operational reductions and static proof artifacts.
- [TrustBoundary.lean](TrustBoundary.lean) and [Action/TrustBoundary.lean](Action/TrustBoundary.lean):
  checked axiom dependencies.

[protocol]: https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md
