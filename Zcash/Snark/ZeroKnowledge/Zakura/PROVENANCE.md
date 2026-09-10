# Zakura 1.4.0 prover target

The target is one version-matched `Proof::create` call for the post-NU6.3
Orchard circuit in Zakura 1.4.0. The prover has eleven IPA rounds, 2,048 rows,
and ten public instance rows per Action. There is no automatic retry or
exceptional-challenge resampling in this call.

The existing fixture formats retain their role as implementation anchors.
Release alignment refreshes the verifier captures from pinned Zakura Rust and
updates the Lean prover model. It does not require new RNG/trace instrumentation
or a universal Rust-to-Lean proof.

## Source and build profile

[release.json](release.json) is the machine-readable provenance record.
It records full source revisions, archive checksums, the selected packages in
the release lockfile, inspected source hashes, and the earlier Lean capture.

| Component | Pin |
| --- | --- |
| Zakura 1.4.0 | [`1e36d1bb6a8a9778a1bd316704b9c8cb75182de6`](https://github.com/zakura-core/zakura/tree/1e36d1bb6a8a9778a1bd316704b9c8cb75182de6) |
| Common 1.2.0 | [`50f712ee22ca95e2dd5230c6f331ce2e433d70ee`](https://github.com/zakura-core/common/tree/50f712ee22ca95e2dd5230c6f331ce2e433d70ee) |
| Published circuit/prover crates | `zakura-orchard`, `zakura-halo2-proofs`, `zakura-halo2-gadgets`, `zakura-pasta-curves`, and `zakura-halo2-legacy-pdqsort`, all at `1.2.0` |
| Reproduction toolchain | Common's `1.97.1`, with its unmodified `Cargo.lock` and `--locked` |
| Circuit and keys | `OrchardCircuitVersion::PostNu6_3`; version-matched proving key and instances |
| Default comparison profile | Orchard `circuit,std,multicore`; Halo2 `batch,multicore,floor-planner-v1-legacy-pdqsort`; `orbits` disabled |
| Serial comparison profile | Defaults disabled; Orchard `circuit,std`; Halo2 `batch,floor-planner-v1-legacy-pdqsort` |
| Platform arithmetic | Portable x86-64; Halo2 also enables Pasta `aarch64-asm` on aarch64 Unix, including macOS and Linux |

The serial profile is an optional comparison configuration, not a claim about
how the distributed node binary was built. Optional backend comparisons must
run natively; cross-compilation alone does not exercise the assembly backend.
The capture feature enables the release's existing verifier exporter.
Neither profile asserts byte-for-byte reproduction of a distributed executable.

`Proof::create` takes a caller-supplied RNG. The API trait does not itself
guarantee unpredictability or independent uniform words. The statistical
theorems assume independent uniform raw bits; a concrete seeded generator
requires a separate computational security premise. Each complete private
schedule has `148m + 46` field samples, each formed from eight 64-bit words.
This is a tape-law statement, not a Rust RNG-cursor correspondence theorem.

## Terminal behavior

All Rust references below use the Common revision pinned above.

| Trigger | Released observation | Source |
| --- | --- | --- |
| Identity public instance commitment | `Error::Transcript`, before the first prover oracle query | [instance initialization](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs#L1152), [identity rejection](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/transcript.rs#L207) |
| Identity proof point before multi-opening | `Error::Transcript`; the Orchard caller receives no partial proof buffer | [transcript writer](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/transcript.rs#L207) |
| Duplicate opening queries at `x = 0` | Returned error after receiving `x1,x2`, mapped to `Error::Opening` | [query check](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/poly/multiopen/prover.rs#L607), [error mapping](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs#L1941) |
| Identity proof point in multi-opening or IPA | `Error::Opening`, through that same mapping | [error mapping](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs#L1941) |
| Zero IPA round challenge | Panic at inverse `unwrap`, after writing both round points | [IPA round](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/poly/commitment/prover.rs#L397) |
| All stages finish | Return the completed proof buffer; completion alone is not verifier acceptance | [Orchard proof call](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/orchard/src/circuit.rs#L1600) |

With multiple workers, Rust prepares advice and draws its blinding randomness
before absorbing the instance commitments. An identity commitment can therefore
be rejected after those draws; the single-worker path rejects it before
synthesis and blinding. See the
[preparation order](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs#L1273).
The one-call observation records the returned outcome and oracle cache, without
the caller's RNG state or synthesis side effects. Its public guard does not
assert that Rust leaves the RNG untouched.

Other exceptional values need not stop the call. In particular, the release
uses an algebraic fallback to evaluate the quotient when `x3` is an opening
node, and a zero-aware grand-product computation. These are existing
computation branches within one call. [MultiopenIpa.lean](../MultiopenIpa.lean)
supplies the actual final polynomial evaluation to the IPA at every point.
Its equality with the verifier's division-based value requires distinct
opening nodes and a later point away from them. The
[collision regression](MultiopenRegression.lean) separates the values `1`
and `0` for the polynomial `1 + X` at the colliding point `0`.
The costed implementation evaluates its stored coefficients by Horner's rule.
These proof changes await elaboration. Rust correspondence remains the existing
[implementation trust boundary](OPTIMIZATIONS.md). Verifier captures anchor
sampled executions; the Lean prover model supplies the zero-knowledge argument.

The scope assumes matching circuit/key versions, matching instance counts,
and satisfying witness rows. Arbitrary malformed requests, allocation failure,
timing, memory/cache accesses, and process-level panic handling are outside
the observation. The panic outcome marks termination of this proof call;
the model supplies no catch-and-retry handler.

## Lean connection

[Attempt.lean](Attempt.lean) observes the terminal result as proof bytes,
returned error, or panic. Multi-opening starts after seven challenge receives,
which fixes the identity-error mapping. [Action.lean](Action.lean) first checks
the actual public initialization points, then executes one reference attempt.
The failed call's partial proof buffer is hidden, while the oracle cache
remains in the adversary's view. Simulator programming failure remains the
explicit `none` outcome of the programmable-oracle experiment; it is not
identified with a Rust error or silently discarded.

`Zcash.Snark.ZeroKnowledge.Zakura.action_simulation_error_bound` compares
`actionProver` and the witness-free `actionSimulator`. Under `ActionZkRelation`,
`m > 0`, `urs.k = 11`, and `urs.w ≠ 0`, its two-sided event bound is
`ε(m) + q_pre/p`. It follows from the existing one-attempt oracle theorem by
the shared public guard and deterministic observation. The simulator uses
ideal uniform private field elements; the real law uses wide reduction.
The two public-rejection laws are identical without querying the oracle.

The new modules and their [direct census](TrustBoundary.lean) await Lean
elaboration. The theorem is about the specified model. As in the earlier
fixture-anchored result, its connection to optimized Rust rests on fixture
checks and source review, with implementation correspondence an explicit
trust boundary. Refreshing the existing verifier captures updates the release
anchor; the changed masking and failure behavior must also match the Lean model.
Existing auxiliary caller-composition theorems are outside this release
claim. Neither this endpoint nor its runner invokes their retry policy.

## Refreshing the existing verifier fixtures

From the formalization repository, using Python 3.11 or later:

```sh
# Local manifest and immutable capture pin; no network and no build.
python3 scripts/check_zakura_release.py

# Authenticate release sources and crates, and compare the stored public data.
python3 scripts/check_zakura_release.py --cache-dir /tmp/zakura-1.4.0-sources --fetch

# Prepare the four existing fixture families; no build or Rust source changes.
python3 scripts/prepare_zakura_release.py \
  --cache-dir /tmp/zakura-1.4.0-sources \
  --output-dir /tmp/zakura-1.4.0-fixtures \
  --suite fixtures \
  --target aarch64-apple-darwin

# Build-dependent: execute the released Rust capture drivers on the native target.
python3 /tmp/zakura-1.4.0-fixtures/run.py
```

Preparation writes an unexecuted plan with one feature report and four exact
capture tests, using default release features and one worker. They emit the
existing single-Action and two-Action honest/random `Fixture.lean` families
and the two random `proof-bytes.hex` siblings. Each output records its intended
repository `destination`; the runner never overwrites the checked-in fixtures.
The honest drivers create a proof with released Rust, replay it through the
released verifier, and export the captured transcript and MSM. The random
drivers use the released fabricate-and-replay path. Lean's existing fixture
checks compare these Rust outputs with its verifier model.

After a successful run, install its outputs through the existing regeneration
entry point; this validates the run record and authenticated source tree before
updating all six files and both provenance manifests:

```sh
scripts/regenerate-fingerprint-fixtures.sh \
  --from-run /tmp/zakura-1.4.0-fixtures \
  --cache-dir /tmp/zakura-1.4.0-sources --update

scripts/check_fixture_manifest.sh
lake build --wfail
```

The regeneration command and CI now target the pinned Zakura sources. Without
`--update`, the command compares captures and fails on any difference. The Lean
build includes `FixtureCheck` and `CircuitCheck`. Capture
equality checks the sampled verifier executions; it does not prove the prover's
randomness law. Source review records the manual comparison of the changed
prover with the Lean definitions. The ZK theorem concerns the Lean model;
its correspondence to the Rust prover remains an implementation assumption.

The runner records toolchain and feature information, exact test results, and
capture hashes. It rejects a filter that executes zero tests. Use a new output
directory for each run. No capture is considered refreshed until that runner
succeeds, the generated files and pins are installed, and Lean checks pass.
Internal archive links to license and documentation files are materialized as
regular files and recorded in the plan; links outside the archive root fail.

The checked-in verifier captures and their manifest entries record the
[pinned Zakura capture run](../../Fixtures/PROVENANCE.md). The source-only
comparison checks all 2,048 coefficient generators, `W`,
`U`, 29 fixed commitments, and 15 permutation commitments against the
single-Action capture. It does not execute release key generation or check
every circuit constraint. The [captured-setup corollary](../ActionInstantiation.lean)
uses its eleven-round and nonidentity blinding-generator certificates.

The separate [circuit/layout dumps](../../../Circuits/Fixtures/PROVENANCE.md)
retain their existing provenance because the circuit is unchanged. The verifier
exporter does not regenerate those JSON files; their original dump tooling is
separate. Their existing Lean reconstruction checks still apply.

## Optional backend regressions

The same preparation script accepts `--suite regressions` to add serial/default,
worker-count, cache, and arithmetic comparisons from the release's existing
tests. These are optional implementation evidence beyond the fixture refresh.
No new RNG/trace instrumentation is included in the release-alignment work.
