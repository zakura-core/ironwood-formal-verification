# Executable PRNG reductions

The PRNG corollaries below prove the complete real-prover-and-test reduction's
resource bound and membership in an operationally defined program class. PRNG
security against that bounded class remains an explicit assumption. It bounds
the tested output advantage `eta`; it does not assume statistical distance
`eta` between the generated tape and a uniform tape.

The release model is [one proof call](Zakura/PROVENANCE.md). The finite retry
and continuing-stream experiments below concern additional external callers
and are outside that model.

| Experiment | Corollary | Two-sided test error |
| --- | --- | --- |
| One interactive attempt | `costedUniformSeedActionZk_test_error_bound` in [CostedInteractivePrng.lean](CostedInteractivePrng.lean) | `epsilon(m) + eta` |
| Finite recorded shared-oracle retries | `costedActionOracleRecordPrng_test_error_bound` in [CostedActionPrng.lean](CostedActionPrng.lean) | `C(m,q) + eta` |
| Complete continuing-generator stream | `costedGeneratedUnlimitedActionOracle_simulation_capstone` in [CostedActionGeneratorStream.lean](CostedActionGeneratorStream.lean) | `2 * (C(m,q) + b(m)^n + eta)` |

Here `m` is the Action count, `q` the initial cache length, and `n` the finite
cutoff used in the stream reduction. The bounds `epsilon`, `C`, and `b` are
defined by [plonkSimulationErrorBound](PlonkSuccessBounds.lean),
[oracleRetryPotential](OracleRetryPotential.lean), and
[actionOracleRetryRate](ActionOracleRetryTail.lean), respectively. The actual generated finite
exhaustion probability is at most `b(m)^n + C(m,q) + eta`. No independence of
generated private blocks or almost-sure seeded termination is assumed.

## Inputs and execution model

[ActionReductionData](ActionReductionData.lean) stores public inputs, the actual
Action setup and compiled key, witness rows, transcript initialization, initial
cache, and auxiliary words. `ofReference` identifies this representation with
the mathematical source inputs. It is a refinement map, not a free preprocessing
operation executed by the reduction. Witness construction and setup/key generation
are outside this stored-input model. Reads and materialization during execution
are included in the proved costs.

The model has explicit prices for field and group operations, stored reads,
comparisons, and canonical coordinate access. Structural operations and bounded
word/byte operations have the prices stated by their component implementations.
This is a checked structural operation count, not a machine-time or Rust
correspondence theorem.

The private candidate input is one stored `148m + 46`-word tape or a stored prefix
of `n` such tapes. Candidate private words are never resampled by a reduction.
Independent fair verifier bits are separate input: `22 * 512` for one interactive
attempt and `n * 22 * 512` for finite recorded retries. The source-law theorems
identify these exact bit-driven computations with the existing wide-challenge
or cached-reply experiments for every fixed candidate private input.

## Concrete test programs

[BooleanTestProgram](BooleanTestCost.lean) is a finite circuit with literal bits,
typed input reads, and NAND gates over previously stored wires. Its interpreter
counts every instruction, indexed wire read, and final output read. Missing wires
read false. The [bound](BooleanTestBound.lean) is proved from this interpreter.

The [recorded-view ports](RecordedTestRead.lean) expose proof bytes, field
challenges, failure status, history and output presence, intermediate and final
caches, both query-address byte strings, raw replies, exhaustion, and stored
auxiliary words. Presence ports distinguish missing entries from present zero
values and distinguish a programming failure from an absent history suffix.
All indexed accesses have [proved traversal bounds](RecordedTestReadBound.lean).
The [regressions](RecordedTestRegression.lean) cover these distinctions, cache
routing, address components, candidate private bits, and shared-wire ordering.

The interactive view is represented by an attempt frame and a second frame
containing the full verifier challenge sequence, including unused challenges
after failure. Its [injectivity theorem](InteractiveViewEncoding.lean) proves
that no original view information is lost. The
[interactive implementation](InteractiveBitsView.lean) constructs this
representation from the complete original prover and canonical observer.

For complete streams, [typed stream ports](StreamTestRead.lean) select individual
history frames and their public caches. A finite circuit has automatic
[measurability and an exact finite-view translation](StreamTestProgram.lean).
There is no assumed host predicate or supplied measurability certificate in the
operational stream corollary.

## Complete reduction and resource class

[ActionReductionProgram](ActionReductionProgram.lean) contains ordinary raw-tape
circuits, full recorded-prover runs followed by view circuits, and Boolean
composition. [InteractiveReductionProgram](InteractiveReductionProgram.lean)
provides the same operations for the single-tape interactive experiment. The
classes contain both constant outcomes, raw candidate-bit tests, and composed
programs; they are not singleton sets containing only the desired reduction.

Every admitted program has executable code and a proved counter bound on every
candidate private tape and verifier-bit outcome. Actual source inputs supply the
input representation premises. Auxiliary copying, the complete real prover,
canonical observation, caches, retained retries, and test execution all contribute
to the budget. No arbitrary callback can enter these program constructors with
an asserted output or a supplied zero-cost counter.

The [recorded source bridge](ActionReductionSource.lean) and
[interactive source bridge](InteractiveReductionSource.lean) prove equality with
the existing PRNG-game reductions and supply their class membership. The derived
budgets are `recordedPrngTimeBound` and `interactivePrngTimeBound`. For the stream
corollary, `recordedPrngViewAndTailTimeBound` is the maximum of the full clipped-view
and exhaustion-test budgets, so one stated PRNG security assumption covers both.

These operational instantiations fix materialized requests, initial caches, and
auxiliary input, and quantify over all concrete circuits of the stated syntax.
The more general theorems with arbitrary probabilistic tests or adaptive
preprocessing/postprocessing remain reduction templates with explicit
admissibility premises. They do not assign a running-time bound to an arbitrary
supplied function. The uniform-bit statistical ZK theorems retain their original,
unrestricted distributional statements.
