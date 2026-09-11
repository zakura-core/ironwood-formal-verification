# Captured prover executions

These fixtures record complete successful one-Action and two-Action proof calls
from the Zakura 1.4.0 prover with an opt-in Rust recorder. Lean reconstructs every
proof message from the captured inputs and compares the ordered transcript and
encoded proof buffer with Rust's output. The existing verifier fixtures independently anchor the same
proofs, challenges, setup, and public inputs.

## Producer and release

[producer.json](producer.json) pins Common commit
[`0b9371b6211780a2e25b140e7a1494759cf077ed`](https://github.com/zakura-core/common/tree/0b9371b6211780a2e25b140e7a1494759cf077ed)
and its source archive. It records the complete file delta from the
[released Common source](../../ZeroKnowledge/Zakura/PROVENANCE.md#source-and-build-profile).
The generator authenticates both archives and rejects any unrecorded difference.
It builds the producer without editing Rust sources or the release lockfile.

The exporter lives in Common:

- Orchard's `prover-fingerprint` feature enables the
  [capture drivers](https://github.com/zakura-core/common/blob/0b9371b6211780a2e25b140e7a1494759cf077ed/crates/orchard/src/circuit/prover_fingerprint.rs).
- Halo2's `unstable-prover-fingerprint` feature enables the
  [recorder and wrappers](https://github.com/zakura-core/common/blob/0b9371b6211780a2e25b140e7a1494759cf077ed/crates/halo2_proofs/src/plonk/prover_fingerprint.rs).
- The verifier capture features remain separate. The drivers compare recorded
  and unrecorded proof bytes and RNG positions, and verify the generated proofs.

The profile uses `PostNu6_3`, eleven IPA rounds, default release features, and
`RAYON_NUM_THREADS=1`. Seeds are `[0x53; 32]` and `[0x4d; 32]`, matching the existing
honest verifier captures. The shared [MANIFEST.tsv](../MANIFEST.tsv) records each
generated Lean file's hash, exporter, source revision, and invocation. The release
record supplies the toolchain and locked dependencies. Each generation run retains
its native target and exact commands in `plan.json`, and its output hashes in
`results.json`.
The producer does not resample challenges or add retries.

## Recorded data and Lean checks

Rust's `dump_vesta_lean_prover_fixture` exports [SingleAction.lean](SingleAction.lean)
and [MultiAction.lean](MultiAction.lean). Ironwood copies these files unchanged.
Each contains setup generators, fixed and permutation rows, public inputs,
synthesized advice rows before masking, ordered RNG method calls, received field
challenges, transcript operations, the terminal result, and the original proof bytes.
The private data belongs to deterministic test witnesses.

[Capture.lean](Capture.lean) independently checks canonical field and curve
representatives, dimensions, byte ranges, and the complete event schedule. Each
field sample consumes eight little-endian 64-bit words; the captures contain
194 and 342 samples. RNG-call counts are also checked at every challenge boundary.

[Replay.lean](Replay.lean) accepts only the input portion. It reconstructs masked
columns, lookup and permutation products, quotient polynomials, commitments,
evaluations, multi-opening, and all IPA rounds. Its
`replay_eq_reference_capstone` theorem identifies this computation with
`plonkReferenceProofFromTape` for every supplied input. The storage and arithmetic
implementations are selected explicitly and proved equal to the reference
operations; they add no compiler substitutions or native-decision axioms.

[Check.lean](Check.lean) compares every emitted point and scalar in order, along
with the challenge markers and successful terminal result. It separately compares
Lean's encoded proof bytes with the original Rust proof buffer. It also compares
the setup, public inputs, initialization, challenges, and transcript with the
existing verifier captures, and commits the captured fixed and permutation rows
to check them against that captured verification key. Expected messages are
comparison targets, never inputs to `replayProof`.

Negative checks change a raw RNG draw, change or reorder messages, truncate or
extend the transcript, and reject truncated events. Byte comparisons must reject
an empty buffer, a changed byte, truncation, and an extra byte. The Rust exporter
also rejects malformed encodings and unsupported event schedules.
The complete execution cases are successful calls; recorder unit tests exercise
error and panic recording, but there are no complete failing-prover captures.

## Scope

The input boundary is Rust's synthesized witness rows. These fixtures do not
prove that Rust and Lean synthesize identical rows for every Orchard witness.
The replay receives the actual challenges. The existing honest verifier fixtures
check the Fiat–Shamir absorb/squeeze schedule against captured prefix/challenge
pairs; the hash outputs come from Rust.

Matching these two executions tests the implementation connection for those
inputs. It does not establish equality of the full Rust and Lean message
distributions or prove that a concrete RNG supplies independent uniform bits.
The general zero-knowledge result remains the theorem about the Lean model,
with its stated randomness assumptions and
[release-model exceptions](../../ZeroKnowledge/Zakura/PROVENANCE.md#reference-model-exceptions).

## Reproduction

From the repository root, with Python 3.11 or later:

```sh
# Check the shared artifact inventory and content hashes; no Rust or Lean build.
scripts/regenerate-prover-fixtures.sh --check-set
scripts/check_fixture_manifest.sh
python3 -m unittest discover -s scripts -p 'test_zakura_*.py'

# Reproduce the two Lean files from the pinned Common exporter and diff them.
scripts/regenerate-prover-fixtures.sh

# Run the complete Lean comparison and its negative checks.
lake env lean --run Zcash/Snark/Fixtures/Prover/Main.lean
```

The shell entry point reuses the verifier fixture regeneration pipeline. It does
not translate Rust data into Lean. `--update` copies the Rust-generated files and
updates the shared manifest only after all Rust commands succeed and the source
tree remains unchanged. Rust verifies both proofs and compares them and their
final RNG positions with unrecorded executions.
`--from-run /path/to/capture-run` reuses a completed run after independently
reconstructing and authenticating its source and command plan, checking the test
logs, and checking each capture against the hash recorded when its command finished.
Modified capture bytes are rejected before installation.

The default `FixtureCheck` target compiles all replay modules and their direct
[trust census](TrustBoundary.lean). Lean CI executes `Main.lean` after the default
build, including when artifacts are restored from cache. The interpreter avoids
eagerly initializing unused finite enumerations in the arithmetic dependencies.
The fixture workflow separately reproduces the Rust captures. These evaluations
are explicit fixture checks, and their results are not added as theorem axioms.
