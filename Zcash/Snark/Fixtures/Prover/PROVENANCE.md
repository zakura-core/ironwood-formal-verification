# Captured prover executions

These fixtures record complete successful one-Action and two-Action proof calls
from the Zakura 1.4.0 prover with an opt-in Rust recorder. Lean reconstructs every
proof message from the captured inputs and compares the ordered transcript with
Rust's output. The existing verifier fixtures independently anchor the same
proofs, challenges, setup, and public inputs.

## Producer and release

[producer.json](producer.json) pins Common commit
[`29beabc8ced6a063abe6ac34cd7b16f0f4907829`](https://github.com/zakura-core/common/tree/29beabc8ced6a063abe6ac34cd7b16f0f4907829)
and its source archive. It records the complete file delta from the
[released Common source](../../ZeroKnowledge/Zakura/PROVENANCE.md#source-and-build-profile).
The generator authenticates both archives and rejects any unrecorded difference.
It builds the producer without editing Rust sources or the release lockfile.

The exporter lives in Common:

- Orchard's `prover-fingerprint` feature enables the
  [capture drivers](https://github.com/zakura-core/common/blob/29beabc8ced6a063abe6ac34cd7b16f0f4907829/crates/orchard/src/circuit/prover_fingerprint.rs).
- Halo2's `unstable-prover-fingerprint` feature enables the
  [recorder and wrappers](https://github.com/zakura-core/common/blob/29beabc8ced6a063abe6ac34cd7b16f0f4907829/crates/halo2_proofs/src/plonk/prover_fingerprint.rs).
- The verifier capture features remain separate. The drivers compare recorded
  and unrecorded proof bytes and RNG positions, and verify the generated proofs.

The profile uses `PostNu6_3`, eleven IPA rounds, default release features, and
`RAYON_NUM_THREADS=1`. Seeds are `[0x53; 32]` and `[0x4d; 32]`, matching the existing
honest verifier captures. [manifest.json](manifest.json) records the toolchain,
profile, generator hashes, artifact hashes, and verifier anchors. Each generation
run retains its native target and exact commands in its `plan.json`.
The producer does not resample challenges or add retries.

## Recorded data and Lean checks

Each compressed binary contains setup generators, fixed and permutation rows,
public inputs, synthesized advice rows before masking, ordered RNG method calls,
received field challenges, transcript operations, and the terminal result.
The private data belongs to deterministic test witnesses.

[Capture.lean](Capture.lean) independently checks the binary framing, canonical
field and curve encodings, dimensions, and the complete event schedule. Each
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
with the challenge markers and successful terminal result. It also compares
the setup, public inputs, initialization, challenges, and transcript with the
existing verifier captures, and commits the captured fixed and permutation rows
to check them against that captured verification key. Expected messages are
comparison targets, never inputs to `replayProof`.

Negative checks change a raw RNG draw, change or reorder messages, truncate or
extend the transcript, and reject malformed encodings and event schedules.
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
# Authenticate local captures and metadata; no Rust or Lean build.
python3 scripts/generate_prover_fixtures.py --check
PYTHONPATH=scripts python3 -m unittest prover_fixture.test_format

# Reproduce both prover captures and the unchanged honest verifier anchors.
python3 scripts/generate_prover_fixtures.py --fetch

# Run the complete Lean comparison and its negative checks.
lake env lean --run Zcash/Snark/Fixtures/Prover/Main.lean
```

`--update` installs captures only after all Rust commands succeed, the source
tree remains unchanged, and the existing verifier anchors match byte for byte.
`--from-run /path/to/capture-run` reuses a completed run after independently
reconstructing and authenticating its source and command plan.

The default `FixtureCheck` target compiles all replay modules and their direct
[trust census](TrustBoundary.lean). Lean CI executes `Main.lean` after the default
build, including when artifacts are restored from cache. The interpreter avoids
eagerly initializing unused finite enumerations in the arithmetic dependencies.
The fixture workflow separately reproduces the Rust captures. These evaluations
are explicit fixture checks, and their results are not added as theorem axioms.
