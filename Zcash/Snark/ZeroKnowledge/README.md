# Ironwood zero knowledge

This directory contains Lean proofs of both:

- **Statistical honest-verifier zero knowledge (HVZK)** for the interactive protocol.
- **Statistical zero knowledge (ZK)** for its Fiat–Shamir transform in the
  **classical programmable random-oracle model**.

The proofs compare the verifier's view with a simulator that receives no private
witness. The reference is the [pinned prover description][protocol]
(Sensei at [56a7de7][sensei]), with `k = 11` and 2,048 rows.

[Results](#main-results) · [Bounds](#error-bounds) ·
[Assumptions](#assumptions-and-scope) · [Build](#build-and-reference)

## Main results

| Result | Start here |
| --- | --- |
| **Interactive HVZK:** statistical comparison of the complete observed attempt, including failed prefixes. | [ActionInstantiation.lean](ActionInstantiation.lean) |
| **Fiat–Shamir ZK:** statistical comparison of the full oracle view, including adaptive queries before and after the attempt. | [ActionFiatShamir.lean](ActionFiatShamir.lean) |
| **Action connection:** construct circuit rows from application witnesses and prove their validity. | [ActionWitnessSimulation.lean](ActionWitnessSimulation.lean) |
| **Retry histories:** finite and unlimited comparisons under the specified retry policies. | [Interactive](ActionRetryLimit.lean), [Fiat–Shamir](ActionOracleStreamSimulation.lean) |
| **Executable simulator:** a fixed-bit implementation with a proved distribution and structural resource bounds. | [ActionOracleBits.lean](ActionOracleBits.lean), [program model](PROGRAMS.md) |
| **PRNG reductions:** computational simulation bounds under explicit generator-security assumptions. | [Interactive](CostedInteractivePrng.lean), [retry streams](CostedActionGeneratorStream.lean) |

The [review packet](REVIEW.md) lists the exact theorem names, compared
experiments, and bounds for every result. Both masking optimizations, the sparse
IPA mask and linear multi-opening mask, are covered jointly with PLONK.

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
See the [full bounds](REVIEW.md) for retries and PRNG reductions.

Each real attempt uses `148m + 46` private field samples; `148m + 70` counts
sampling-bias costs in the comparison, not the private tape length.

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
- **Retries:** a fixed request and the stated freshness, cache, and retry-rate
  conditions. Oracle retries permit no intervening adversary queries.

Fiat–Shamir uses a classical programmable random oracle. Concrete BLAKE2b
security, whole-program Rust equivalence, and machine-instruction timing are
outside these protocol and structural-cost theorems.

## Build and reference

From the repository root:

```sh
lake build --wfail
```

The default build includes this development and its trust census.

- [REVIEW.md](REVIEW.md): theorem index, exact bounds, assumptions, and review evidence.
- [PROGRAMS.md](PROGRAMS.md): executable programs and the resource model.
- [Computability boundary](../../../book/src/formal-verification/zero-knowledge.md):
  operational reductions and static proof artifacts.
- [TrustBoundary.lean](TrustBoundary.lean) and [Action/TrustBoundary.lean](Action/TrustBoundary.lean):
  checked axiom dependencies.

[protocol]: https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md
[sensei]: https://github.com/tachyon-zcash/bento/tree/56a7de7474da3b86fa475f01400edadfd8af4cb6/crates/sensei
