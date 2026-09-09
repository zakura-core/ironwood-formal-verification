# ZK review packet

Proof baseline: `de8910f038852ad6fdb8c3748479df1ffe288946` on `establish-zk` in
[the private PR](https://github.com/TalDerei/ironwood-private/pull/1).
The claims below concern that checked Lean development and its specified
experiments. Independent review is pending.

The target is the [pinned prover description](https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md)
and the repository's reference computation. The description's Sensei revision is
[Bento `56a7de7474da3b86fa475f01400edadfd8af4cb6`](https://github.com/tachyon-zcash/bento/tree/56a7de7474da3b86fa475f01400edadfd8af4cb6/crates/sensei).
Identifying that source does not assert whole-program Rust equivalence.

**Claims and exact experiments**

All theorem names in this packet are in `Zcash.Snark.ZeroKnowledge`.
`PMFEventBiasLE` bounds every event-probability difference in one direction;
`MeasureEventBiasLE` does so for measurable events of complete stream laws.
The simulation results provide both directions. The PRNG results instead bound
the Boolean output of an admitted test under an explicit security assumption.

| Claim | Theorem and source | Compared laws |
| --- | --- | --- |
| One complete interactive Action attempt, error `epsilon(m)` | `wideActionZkRelation_simulation_error_bound` in [ActionInstantiation.lean](ActionInstantiation.lean), using [the actual compiler theorem](ActionCompilerSimulation.lean) | `actionZkProver` and `actionZkSimulator` |
| Unlimited independent interactive retries, error `epsilon(m)/(1-F(m))` | `wideUnlimitedActionZk_simulation_error_bound` in [ActionRetryLimit.lean](ActionRetryLimit.lean) | `actionZkRetryProver` and `actionZkRetrySimulator` |
| One-attempt programmable-oracle simulation, error `epsilon(m)+q_pre/p` | `actionFiatShamir_simulation_error_bound` in [ActionFiatShamir.lean](ActionFiatShamir.lean) | `actionOracleRealExperiment` and `actionOracleSimulatedExperiment` |
| One-attempt fixed-bit simulator, error `epsilon_bits(m,q_pre)` | `actionFiatShamirBits_simulation_error_bound` in [ActionFiatShamirBits.lean](ActionFiatShamirBits.lean) | `actionOracleRealExperiment` and `actionOracleBitSimulatedExperiment` |
| Every finite shared-oracle retry budget, error `R(m,q_pre,n)` | `actionFiatShamirRetry_simulation_error_bound` in [ActionFiatShamirRetry.lean](ActionFiatShamirRetry.lean) | `actionOracleRetryRealExperiment` and `actionOracleRetrySimulatedExperiment` |
| Complete shared-oracle retry stream for a fixed request, error `C(m,q)` | `wideUnlimitedActionOracle_simulation_capstone` in [ActionOracleStreamSimulation.lean](ActionOracleStreamSimulation.lean) | `actionOracleRetryStream` and `actionOracleBitRetryStream` |
| One seeded interactive attempt, test error `epsilon(m)+eta` | `uniformSeedActionZk_test_error_bound` in [ActionPrngSecurity.lean](ActionPrngSecurity.lean) | Auxiliary-data mixtures of tested `actionZkProverFromSource` and `actionZkSimulator` |
| Finite retries from one continuing generator, test error `R(m,q_pre,n)+eta` | `generatedActionFiatShamirRetry_test_error_bound` in [ActionGeneratorPrng.lean](ActionGeneratorPrng.lean) | Tested `actionGeneratedOracleRetryExperiment` and `actionOracleRetrySimulatedExperiment` |
| Complete seeded retry stream for a fixed request, test error `2(C(m,q)+b(m)^n+eta)` | `generatedUnlimitedActionOracle_simulation_capstone` in [ActionGeneratorStreamPrng.lean](ActionGeneratorStreamPrng.lean) | Tested `actionGeneratedOracleRetryStream` and `actionOracleBitRetryStream` |

The one-attempt ideal-field simulator has an explicit computable tape program;
`actionOracleSimulatorProgram_law` in [ActionOracleSimulator.lean](ActionOracleSimulator.lean)
identifies its law with the model used above. The fixed-bit implementation has
its own additional sampling term and [exact bit-tape law](ActionOracleBits.lean).

**Premises and observations to check**

- `ActionZkRelation` requires the original Action gate and lookup equations and
  the concrete compiler's copy equations. The Action circuit, key, masking
  profile, selector boundaries, commitment routing, and canonical codecs are
  already connected. Constructing those satisfying rows from an application-level
  `ActionSpec` witness remains separate correctness work.
- Setup premises are `urs.k = 11` and `urs.w != 0`. The
  [captured-setup corollary](ActionInstantiation.lean) supplies them for its named
  URS; it does not prove a parameter-generation procedure. Theorems use the stated
  `Fintype VestaG` instance.
- The interactive real view includes the verifier challenge tape, emitted prefix,
  and status. Uniform raw private words reproduce the entire specified
  wide-reduced tape law; independence is a joint sampling premise. Exceptional
  challenges and observed failures are retained. No conditioning on acceptance
  or suppression of completed-but-rejected output is part of these comparisons.
- Oracle experiments use a classical programmable random oracle, with adaptive
  preprocessing and postprocessing and the retained final cache. The proof routine
  receives the public request after witness erasure; the adversary keeps its
  auxiliary data. [ByteFiatShamir.lean](ByteFiatShamir.lean) and
  [ActionFiatShamir.lean](ActionFiatShamir.lean) connect personalization, public-input
  prefix, scalar/affine-point bytes, markers, squeeze order, and raw digest
  reduction to the verifier schedule. Concrete BLAKE2b is outside the oracle proof.
- Retry policy: only `.failed .retryRandomness` continues. Completion,
  `.failed .coincidentOpeningQueries`, and simulator programming failure stop.
  Ordinary failures retain their prefix; programming failure is `none` and
  preserves the prior cache. Finite exhaustion is explicit, including budget zero.
  The finite [history law](ActionOracleRetry.lean) compares the history and cache
  before arbitrary postprocessing. The request stays fixed; there are no
  intervening adversary queries during the internal retry run.
- Unlimited interactive retries use fresh independent private and verifier tapes.
  Normalization and vanishing exhaustion tails require `B(m) < 1`; `m <= 65535`
  is a checked sufficient condition, not a protocol maximum.
- Complete shared-oracle streams fix one valid request and retain every result
  and intermediate public cache, including a possible infinite run. The prior
  cache is arbitrary; there are no intervening adversary queries. Fresh private
  and oracle reply tapes realize the existing cached execution. The uniform
  bound `C(m,q)` uses only the simulator's state-uniform retry rate `b(m) <= 1/2`;
  `1 <= m <= 65535` supplies it. The cylinder limit covers every measurable event
  without discarding nontermination. The simulator terminates almost surely;
  real nontermination has mass at most `C(m,q)`. Truncation after `n` attempts
  costs at most `b(m)^n` for the simulator and `b(m)^n + C(m,q)` for the real law.
  See [the complete laws](ActionOracleStream.lean) and
  [termination theorems](ActionOracleStreamTermination.lean). This fixed-request
  theorem does not itself instantiate adaptive before/after processing. The
  continuing-generator extension has its own PRNG reduction below.
- The [PRNG game](PrngSecurity.lean) samples a uniform bit seed independently of
  preprocessing and retained auxiliary data. Security is relative to an explicit
  admissible test class. Membership of the entire prover/retry/postprocessing
  reduction is a premise. No statistical closeness of a seeded tape, concrete
  generator security, or efficient-test membership is inferred from wide reduction.
- The [continuing-generator runner](ActionGeneratorRetry.lean) initializes once
  per experiment. Each started attempt consumes a whole private block and discards
  unused words in that block. Terminal output stops before the next block.
  Exact replay and state-advance identities hold even for correlated generator
  output. The private final generator state is omitted from the verifier view.
  This is the specified allocation policy, with no Rust cursor correspondence claim.
- The [complete seeded Action law](ActionGeneratorStream.lean) initializes once
  from a fresh uniform bit seed and uses an independent infinite public reply
  stream. Every finite projection is exactly the recorded continuing-generator
  runner. The request and initial public cache are fixed. At cutoff `n`, both
  [whole-prefix reductions](ActionOracleRecordedPrng.lean) must be admitted: the
  test of the clipped complete view and the actual finite exhaustion bit. Their
  common PRNG advantage `eta` is charged twice. The generated exhaustion and
  [nontermination mass](ActionGeneratorStreamTermination.lean) are each at most
  `b(m)^n + C(m,q) + eta`. No per-seed stopping or independent generated-block
  assumption is introduced, and the infinite nontermination event need not itself
  belong to the PRNG test class. The tested comparison requires a measurable view
  test. This theorem does not instantiate adaptive preprocessing/postprocessing
  on the infinite stream or prove either reduction's machine running time.

**Bounds and resource accounting**

Here `p` is the Vesta scalar-field order, `m` the Action count, `q_pre` the number
of preprocessing queries, and `n` the finite attempt budget. Fiat–Shamir comparisons
require `m > 0`. Natural subtraction makes `n(n-1)` zero when `n = 0`.

```text
2^512 = Qp + r
delta = r(p-r)/(p * 2^512) <= 2^-260

epsilon(m) = (42882m + 4113)/p + (148m + 70) delta
           < m * 2^-238, m >= 1

F(m) = (22m + 45)/p + (148m + 68) delta
B(m) = F(m) + epsilon(m)

epsilon_bits(m,q) = epsilon(m) + (132m + 36) delta + q/p
                  = (42882m + 4113 + q)/p + (280m + 106) delta

R(m,q,n) = n * epsilon_bits(m,q) + 11n(n-1)/p
         <= n*m*2^-238 + (n*q + 11n(n-1))/p, m >= 1

b(m) = B(m) + (132m + 36) delta
C(m,q) = 2 * epsilon_bits(m,q + 22)
       < 2 * (m*2^-238 + (q + 22)/p), m >= 1

E_seeded_infinite(m,q,n) = 2 * (C(m,q) + b(m)^n + eta)
```

`F` bounds failure to finish the emission schedule and hence the retry probability.
Finishing that schedule does not assert verifier acceptance. The binary certificates
are in [PlonkBinaryBounds.lean](PlonkBinaryBounds.lean),
[OracleBitBounds.lean](OracleBitBounds.lean), [OracleRetryBounds.lean](OracleRetryBounds.lean),
and [OracleRetryPotential.lean](OracleRetryPotential.lean). The shared-oracle
retry-rate certificate is in [ActionOracleRetryGeometric.lean](ActionOracleRetryGeometric.lean).

| Resource | Checked amount |
| --- | --- |
| Real private words per started attempt | `148m + 46` raw 512-bit words |
| Ideal-field oracle simulator per attempt | 22 raw 512-bit challenge words and `132m + 36` uniform fields |
| Fixed-bit oracle simulator per attempt | `512 * (132m + 58)` input bits |
| Real private prefix covered by the finite PRNG assumption | `512 * n * (148m + 46)` bits |
| Final cache after finite shared-oracle retries and postprocessing | At most `q_pre + 22n + q_post` entries |

The `148m + 70` coefficient belongs to the comparison, not the real tape count.
The finite PRNG loss `eta` covers the whole candidate prefix and admitted test,
even when a particular execution uses fewer blocks. [The explicit encoding](ActionPrivateRetryBits.lean)
identifies that raw prefix with a fixed bit string. These are input and query
budgets. The arithmetic and cache components below have checked structural
costs. Whole-simulator composition and the real-prover-and-test runtime needed
for PRNG test-class membership remain open; no machine-code correspondence is
asserted.

**Application witness construction**

[ActionWitnessConditions.lean](ActionWitnessConditions.lean) starts from
`ActionSpec` and makes the constructor's extra input conditions explicit:
Sinsemilla hashes are defined, the literal Merkle children are canonical base-field
encodings, and the five scalar representatives fit the current one-field Nat-hint
interface. These conditions are stronger than the guarded application specification
alone; they are not additional hypotheses of the existing circuit-level ZK theorem.
`actionWitnessConditions_proverAssumptions` derives the existing circuit's semantic
honest-prover preconditions for the normalized application data.

[ActionWitnessNormalization.lean](ActionWitnessNormalization.lean) preserves
`ActionSpec` and every semantic scalar while deriving auxiliary windows and Merkle
readings. [ActionWitnessHints.lean](ActionWitnessHints.lean) proves that the actual
fixed hint program decodes the encoded data in every cell environment.
[ActionWitnessHintWindows.lean](ActionWitnessHintWindows.lean) connects its actual
window programs to exact scalar reconstruction. The defined canonical Merkle fold
and its two 16-layer halves are checked against the literal path statement.

[ActionWitnessRows.lean](ActionWitnessRows.lean) defines a computable constructor
using the actual circuit operations, V1 placement, fixed columns, and public-input
layout. `actionWitnessAssignment_environment` identifies the executed environment
with the canonical environment reconstructed from its advice, and
`actionWitnessAssignment_publicInput` preserves the supplied public statement.
The interpreter's frame properties are proved in
[AdviceWitnessExecution.lean](AdviceWitnessExecution.lean) and
[AdviceWitnessAssignment.lean](AdviceWitnessAssignment.lean).

[AdviceWitnessEquations.lean](AdviceWitnessEquations.lean) now identifies the
collected advice equations with the original source witness clauses. The canonical
compiler discharges every remaining fixed-write and table clause in
[CompiledFixedWitnesses.lean](CompiledFixedWitnesses.lean). The
[trace refinement](AdviceWitnessTrace.lean) proves every original witness equation
when reads are causal and each write preserves established values. Its
[checked alias plan](AdviceAliasPlan.lean) accepts a repeated target only for a
certified copy whose source has the same established value. This route does not
require distinct targets. The [structured-program dependency theorem](WitnessProgramSupport.lean)
and [builder support](WitnessBuilderSupport.lean) cover local steps, branches,
dynamic indexing, vectors, and the original value, scalar, Nat, and Boolean builders.

[ActionNativeRouting.lean](ActionNativeRouting.lean) connects every collected copy
annotation to the original complete Action source. The proof checks the actual
shared base columns, both incomplete multiplication halves, and the region schedule
that places their multiplier at region 297. All native annotations have exact
copy semantics for every environment; the structured IR recognizer supplies the
remaining copy sources. This certificate neither proves nor assumes successful
execution of the global alias and read plans.

The [function-support certificates](WitnessFunctionSupport.lean) cover the
original native witness functions for Poseidon, incomplete and fixed-base
multiplication, note commitment and canonicity, CommitIvk, Sinsemilla, and Merkle
layers. Each proof keeps the actual source function and all arithmetic values;
nested callbacks retain explicit support premises. The
[fixed Action hints](ActionHintReadSupport.lean), scalar windows, and original
Merkle sibling and swap callbacks read no cells. The
[annotation checker](AdviceSupportPlan.lean) proves causality from a successful
availability scan and derives the original witness equations when exact source
erasure, alias checking, and semantic copy provenance also hold.

[AdviceAliasAddressPlan.lean](AdviceAliasAddressPlan.lean) proves that alias
decisions depend only on targets and copy addresses. The
[finite-map representation](AdviceAliasMap.lean) retains every column kind, index,
and signed row. The [alias-map checker](AdviceAliasMapPlan.lean) and
[read-map checker](AdviceSupportMapPlan.lean) preserve all results of the original
scans, including rejection, and supply the same compiler witness-equation
interface. These are checker refinements; they do not assume a successful Action
certificate or change its source program.

[AdviceMapScan.lean](AdviceMapScan.lean) exposes exact option-valued transitions
for both policies and proves equality with the original scans. Its
[bounded checker](../../Meta/AdviceMapScan.lean) normalizes and kernel-checks
intermediate maps, then checks and composes the exact continuations. No compiled
evaluator supplies a trusted Boolean answer. Regression checks force boundaries
between every entry, accepting available reads and equal-root copies while
rejecting future reads, fresh-write collisions, and conflicting roots. The full
Action scans remain an outstanding instantiation of this checked mechanism.

[AdviceSourceCertificate.lean](AdviceSourceCertificate.lean) retains the original
instructions and copy tags with their semantic read annotations. Its finite-data
constructor requires equality to the original addresses, reads, and tags. Source
transport changes proof metadata while leaving the stored data directly evaluable.
The [proof-producing elaborator](../../Meta/AdviceSourceCertificate.lean) applies
source equations and support lemmas; its completed certificate is checked by the
kernel. [Adversarial checks](../../Meta/Tests/AdviceSourceCertificate.lean) reject
omitted reads, unavailable reads, and changed source addresses.

Native support agreement also retains the immutable public and fixed environment.
This supplies a certificate for the original absolute-row `instanceGet` callback;
its row is not represented as a region-relative advice read. The execution theorem
already supplies non-advice equality, so this introduces no new execution premise.
The regression suite accepts a public read at nonzero placement and rejects
agreement across different public inputs.

[ActionWitnessLoadCertificate.lean](ActionWitnessLoadCertificate.lean) instantiates
that interface for all eleven original instructions in the eight-region loading
stage. Both finite scans are kernel checked at the proved Action placement. This
is a static proof artifact with code generation disabled for expanded kernel-only
source auxiliaries; the original witness constructor remains executable.

[ActionValueWitnessCertificate.lean](ActionValueWitnessCertificate.lean) covers
all 1,083 original instructions of the value-commitment stage for arbitrary stage
inputs. The short and full-width multiplications and complete addition retain
their exact source programs. Named structured wrappers use the general IR
support theorem, with regression checks retaining unavailable reads and rejecting
unknown native callbacks. This stage inherits the existing named Pallas
generator-order certificate. Its read availability still belongs to the global
Action scan.

[ActionWitnessReadings.lean](ActionWitnessReadings.lean) isolates exactly the
private readings used by the original completeness preconditions: eight fields,
six points, five scalar/window pairs, and the first 32 auxiliary Merkle readings.
It proves invariance of those preconditions without requiring equality of unused
decomposition exports or auxiliary tail values. The stronger complete-observation
interface remains in [ActionWitnessObservation.lean](ActionWitnessObservation.lean).

[ActionWitnessExtraction.lean](ActionWitnessExtraction.lean) proves the required
agreement for the actual generated assignment, assuming its original witness
equations. It combines the original loaders, five full-width scalar routes, and
two 16-layer Merkle calls with the checked hint decoding and canonical windows.
[ActionWitnessCompleteness.lean](ActionWitnessCompleteness.lean) then transfers
the application's conditions and preserved public inputs to the original
top-level completeness theorem. Its conclusion is the original operation
constraints, under the same witness-equation premise.

The complete certified annotation list and global scans must still discharge
that premise. [CompiledGateCompleteness.lean](CompiledGateCompleteness.lean)
derives all compiled gates from the operation equations, positive selector
degree, and an explicit finite activation-coverage condition. Source identities
retain gate names as well as selector indices; the actual coverage scan is still
required. [ActionQueryRows.lean](ActionQueryRows.lean) interprets the generated
assignment on every row before the final cyclic row, including the signed
previous-row read at zero. [ActionQueryValuation.lean](ActionQueryValuation.lean)
and [InactiveGateCompleteness.lean](InactiveGateCompleteness.lean) handle the
unused suffix without requiring agreement of wrapped private reads.

[CopySourceCompleteness.lean](CopySourceCompleteness.lean) proves every equation
of the ordered raw compiler copy stream. Deferred constants retain their
positional allocation and the exact value in the actual fixed environment.
[ActionCopyValues.lean](ActionCopyValues.lean) identifies those values with the
prover's actual packed cells using the complete query routes.
[ActionLookupValues.lean](ActionLookupValues.lean) carries paired lookup tuples
through selector compression and query compilation. Active rows use an explicit
source-coverage premise; inactive rows use the actual zero-index table entry,
including the Sinsemilla generator coordinates.
[ActionGateValues.lean](ActionGateValues.lean) establishes every compiled gate
row, and [ActionRowRelations.lean](ActionRowRelations.lean) preserves both kinds
of row relation through the reference-key shape.
[ActionConstraintsRelation.lean](ActionConstraintsRelation.lean) combines these
three bridges into `ActionZkRelation` under the original constraints and explicit
activation-coverage checks. The complete advice scans,
actual gate and lookup activation coverage, and final application-level
`ActionZkRelation` corollary remain open. The existing circuit-level simulation
theorem and validity relation are unchanged.

**Byte-cache execution costs**

[ByteEqualityCost.lean](ByteEqualityCost.lean),
[OracleCacheCost.lean](OracleCacheCost.lean), and
[OracleProgrammingCost.lean](OracleProgrammingCost.lean) implement the existing
byte equality, first-match lookup, and collision-rejecting programming operations
with structural counters. Each erasure theorem preserves the exact return value.
Counters remain outside failure options, retaining work on every stopped prefix.
Inputs are materialized finite byte lists and query logs; the cost units charge
byte comparisons, structural case tests, and cache-cell construction.

The [protocol size bounds](PlonkTranscriptSize.lean) follow the original absorb
order, allowing all optional permutation evaluations without a well-formedness
premise. [ActionCacheCost.lean](ActionCacheCost.lean) uses the actual public prefix
and eleven-round schedule to prove a bound of
`22 * ((q + 22) * (9490m + 14207) + 4) + 2` for programming one materialized view.
The parameters are `m` Actions and `q` initially cached entries. No successful
emission or nonzero-challenge premise is needed. This is a cache-component cost
proof; public-input preparation, bit packing, field/group/polynomial arithmetic,
encoding, observation, and full simulator/reduction composition remain outside it.

**IPA and PLONK arithmetic costs**

[IpaSimulatorCost.lean](IpaSimulatorCost.lean) constructs the complete IPA
transcript and materializes every output, including fields originally represented
as functions. `materializedIpaSimulatorCosted_result` identifies exactly the
existing simulator's finite observation; `materializedIpaSimulatorCosted_cost_le`
bounds the same counted algorithm. The budget retains both public folds, the
scalar case test, every round point, the mask commitment, both responses, and
all supplied public-input and coin-reader costs. It holds at exceptional challenge
values and includes materialization work before any later encoder failure.

[ExpressionCost.lean](ExpressionCost.lean) counts every original AST node and query
access. [ExpressionCompressionCost.lean](ExpressionCompressionCost.lean) composes
those evaluations into the actual ordered lookup fold. The complete five-value
[lookup calculation](LookupExpressionsCost.lean) and both
[permutation-chunk products](PermutationChunkCost.lean) retain their existing
formulas and inactive-row behavior. [PolynomialArithmeticCost.lean](PolynomialArithmeticCost.lean)
loads the actual canonical coefficient array and proves its counted Horner
algorithm equal to the existing evaluator. [CommitmentArithmeticCost.lean](CommitmentArithmeticCost.lean)
counts the full coefficient/generator sweep and the public commitment and scalar
claim folds. The [complete permutation calculation](PermutationExpressionsCost.lean)
includes first, last, and inter-set constraints. [Constraint assembly](ConstraintAssemblyCost.lean)
and [cross-Action collection](ConstraintCollectionCost.lean) preserve the entire
ordered list and retain all provider costs. The [Lagrange basis](LagrangeBasisCost.lean),
[quotient fold](QuotientEvaluationCost.lean), and [query routers](QueryRoutingCost.lean)
also have exact counted implementations, including exceptional values and defaults.
The [full Lagrange interpolant](LagrangeEvaluationCost.lean) and
[multi-opening scalar evaluation](MultiopenEvaluationCost.lean) include both
interpolation loops and the denominator product. A
[direct commitment/scalar fold](MultiopenCombinationCost.lean) is proved equal
to evaluating the existing symbolic MSM combination. The
[actual private-column schedule](PrivateColumnOrderCost.lean),
[disclosed-value routing](PrivateColumnRoutingCost.lean), and
[commitment-entry routing](CommitmentEntryCost.lean) charge schedule construction,
equality search, and the complete selected readers.

[PlonkMaskSimulatorCost.lean](PlonkMaskSimulatorCost.lean) computes every
commitment and private-column observation in the original pre-IPA simulator.
Its result is the fully materialized finite view, and the counter retains all
coin reads and point multiplications. [Opening layouts](OpeningGroupLayoutCost.lean)
and [query-order tables](QueryOrderCost.lean) preserve the exact original order.
[Private-group evaluations](PrivateOpeningEvaluationCost.lean) include all column
routing and scalar folds. [Public opening claims](PublicOpeningClaimsCost.lean)
include the complete row-polynomial preparation and fixed-query routing.
The [collapsed quotient point](CollapsedQuotientPointCost.lean) counts every
original piece weight and point read.

[PublicOpeningCost.lean](PublicOpeningCost.lean) composes the complete public
opening. It reconstructs all five [group commitments](OpeningCommitmentVectorCost.lean),
all [node and group scalars](OpeningScalarVectorsCost.lean), and the original
[point sets](OpeningPointSetsCost.lean), then executes interpolation and the
final point/scalar fold. Erasure identifies the existing public opening after
evaluation of its symbolic MSM. [PublicOpeningCostBound.lean](PublicOpeningCostBound.lean)
substitutes the checked component budgets into one explicit bound. All public
row-polynomial preparation, materialized vector construction, indexed reads,
and field/group operations remain in that bound. Exceptional field values and
zero defaults retain the reference semantics. The inferred quotient value is
a supplied scalar with its complete cost; the following layer computes it.

[PlonkClaimConstraintsCost.lean](PlonkClaimConstraintsCost.lean) constructs the
actual fixed, advice, instance, and sigma queries, all three permutation records,
their resolved column pairs, and all three lookup inputs. Its result is the
existing verifier constraint list at the original claim proof.
[PlonkClaimInputBounds.lean](PlonkClaimInputBounds.lean) derives stored-field
access and list sizes from those constructors. The
[complete constraint bound](PlonkClaimConstraintsCostBound.lean) uses the actual
gate trees, lookup trees, and key layout, retaining all preparation costs.

[PlonkVerifierHxCost.lean](PlonkVerifierHxCost.lean) composes domain powering,
all Lagrange values, complete claim and constraint preparation, output-list
materialization, and the final quotient fold and division. Erasure is exactly
`plonkVerifierHx` for the original public row polynomials and disclosed columns.
The [total quotient bound](PlonkVerifierHxCostBound.lean) counts this same
computation, including exceptional challenge values. Supplied row, key-tree,
observation, and challenge readers retain their complete costs. The concrete
stored input representations are described below; whole-simulator composition
remains separate.

[StoredRowsCost.lean](StoredRowsCost.lean) charges both levels of matrix lookup
and recovers the original materialized finite vectors. [ActionPublicInputCost.lean](ActionPublicInputCost.lean)
serializes the ten actual public fields and prices all preparation and row access,
including zero padding. [StoredPlonkSetupCost.lean](StoredPlonkSetupCost.lean)
stores all 2048 generators, 29 fixed columns, and 15 sigma columns; its read bounds
follow from those dimensions. [StoredPlonkKeyCost.lean](StoredPlonkKeyCost.lean)
stores the original gate trees, permutation layout, and three lookup input/table
lists. Returning a stored reference pays for the read; subsequent tree and column
traversals remain in the evaluator's cost. These representations are supplied
inputs, so no setup or key-generation algorithm is treated as a free callback.

The model uses materialized arrays and lists, bounded-width structural indexing,
and explicit prices for field and group primitives. Callback readers carry their
complete costs. Shared intermediate work may be conservatively counted more than
once. The [public row coefficient construction](RowCoefficientCost.lean) uses the
proved inverse-DFT formula. [Row evaluations and commitments](RowPolynomialCost.lean)
include every coefficient calculation and retain full row-provider costs.
These component proofs still need codecs, transcript observation, and their
composition into `actionOracleSimulatorFromBits`. A PRNG reduction
executes the real prover and the supplied view test, so its admissibility needs
those runtime bounds in addition to simulator efficiency.

**Input conversion costs**

[StoredBitTapeCost.lean](StoredBitTapeCost.lean) reads materialized Boolean lists
with complete traversal costs and charges construction of each word/bit index.
Its raw and reduced materializers are proved equal to every entry of the existing
fixed-tape conversion. For `N` words, `L` stored bits, and primitive read price `R`,
raw conversion costs at most `N * (512 * (2L + R + 4) + 264195) + N^2 + 1`;
direct field conversion replaces `264195` by `264194`. The bound covers the entire
converted output. Later challenge/private-tape routing remains to be composed.

[RawBitPackingCost.lean](RawBitPackingCost.lean) counts little-endian packing from a
reader that supplies its complete bit-access costs. [WideBitReductionCost.lean](WideBitReductionCost.lean)
uses field Horner evaluation and proves exactly the same result as packing followed
by the specified modular reduction. The word-level results equal the existing
`rawBitsTapeEquiv` and `reduceFieldTape` values for every input tape. The algorithms
retain reader costs and successor-index adapter costs; case tests, Boolean branches,
and the two bounded-width arithmetic operations per bit each cost one unit.

For a 512-bit word and reader accesses bounded by `R`, either component costs at
most `512R + 264193` structural units. The field reducer uses fixed Pasta-field
addition units. Counters are accounting metadata. A concrete reader representation,
primitive-to-machine cost correspondence, the complete tape-access pattern, and
composition with the full simulator still require their own proofs. These results
do not discharge the PRNG test-class resource premise.

**Validation and review status**

The [validation record](review/validation-915317a1.log) contains the successful
full default-target build (`lake build --wfail`, 4,454 jobs), repository guards,
and the [32-declaration dependency inventory](review/axioms-915317a1.log) for the
source-certificate and input-cost milestone. The subsequent value-commitment
milestone passed [the full 4,455-job build and guards](review/validation-6281a298.log).
Both new mathematical declarations have direct pins and an
[exact axiom inventory](review/axioms-6281a298.log); their only native dependency is
the existing Pallas generator-order certificate below. The ten metaprogram
regression declarations are pinned in their test module. No admission or new
native-evaluation certificate was introduced at that milestone.

The application extraction and completeness checkpoint passed
[the full 4,465-job build and guards](review/validation-b3b22e26.log), with
[32 new mathematical declarations](review/axioms-b3b22e26.log) each directly pinned.
Its 14 source-certificate regression declarations also pass their direct checks.
All 928 modules are covered by default targets and all 326 endpoint declarations
are pinned. The new declarations inherit only the existing Pallas native owner;
no admission or new native certificate was introduced. The full
[parent](TrustBoundary.lean) and [Action](Action/TrustBoundary.lean) boundaries also
check the earlier milestones.
The next compiler and query checkpoint passed the
[focused 3,691-job build and guards](review/validation-6fba8271.log), with
[57 new mathematical declarations](review/axioms-6fba8271.log) across eleven
modules, each directly pinned. All nine source-list and fourteen advice-source
regressions passed, and both original stage certificates were rebuilt after the
shared reflection change. This checkpoint has no new axiom or native owner.
The complete Action source certificates are still under construction, so this
record claims a focused build; the latest full workspace build remains the
preceding extraction checkpoint.

The Action row checkpoint passed the
[focused 3,700-job build and guards](review/validation-fb1c737e.log). All
[35 new declarations across nine modules](review/axioms-fb1c737e.log) have direct
pins and a separate dependency inventory. This closes the actual lookup-tuple
and packed-copy bridges under the stated source premises. Its only native
owner is the existing Pallas certificate; the full source scans remain pending.

The arithmetic milestone passed the
[focused 3,728-job build and guards](review/validation-1e80ffcc.log). All
[118 new declarations across fourteen modules](review/axioms-1e80ffcc.log) have
exactly one direct pin and a separate transitive inventory. The thirteen runtime
modules use only Lean's standard axioms; the Action relation composition retains
the existing Pallas certificate. The full Action source checks and complete
simulator/reduction runtime composition remain open.

The constraint and certificate-generation checkpoint passed the
[focused 3,739-job build and guards](review/validation-c55b3ea1.log). All
[80 new declarations across ten runtime modules](review/axioms-c55b3ea1.log) have
one direct pin and a separate inventory containing only standard axioms. Both
original stage certificates and all source-certificate regressions passed after
switching to synchronously checked proof pieces. The full Action source
certificates remain in progress, so this checkpoint does not claim a full build.

The opening-cost checkpoint passed the
[focused 3,747-job build and guards](review/validation-7756fd3e.log). All
[62 declarations across eight modules](review/axioms-7756fd3e.log) have exactly
one direct pin and a separate inventory containing only standard axioms. This
adds both Lagrange interpolation loops, complete multi-opening scalar evaluation,
the direct commitment/scalar combination, and actual private-column and entry
routing. Complete opening assembly and whole-program costs remain open.

The public-polynomial checkpoint passed the
[focused 3,750-job build and guards](review/validation-084e9f2a.log). All
[19 declarations across three modules](review/axioms-084e9f2a.log) have direct
pins and separate inventories containing only standard axioms. Public polynomial
coefficients are now constructed from their rows with explicit cost bounds;
evaluation and commitment include that preparation. Complete-multiplication
wrapper support and all source regressions passed, and both original stage
certificates were rebuilt. Full Action source scans remain in progress.

The mask and opening-claims checkpoint passed the
[focused 3,756-job build and guards](review/validation-bb756ffc.log). All
[38 declarations across six modules](review/axioms-bb756ffc.log) have direct
pins and a separate inventory containing only standard axioms. The complete
PLONK mask view is materialized with a checked cost bound. Opening layouts,
exact query tables, complete private-group evaluations, public first-group claims,
and the collapsed quotient point retain their actual preparation and routing costs.
Commitment and node reconstruction and the final simulator composition remain open.

The complete public-opening checkpoint passed the
[focused 3,767-job build and guards](review/validation-d87d93ed.log). All
[66 declarations across eleven modules](review/axioms-d87d93ed.log) have direct
pins and separate inventories containing only standard axioms. The counted
construction includes all polynomial, commitment, node, and group preparation,
interpolation, and the final commitment/scalar fold. Its result equals the
reference public opening and satisfies an explicit total cost bound. That checkpoint left
query-provider and quotient composition to the subsequent layer above. Concrete
input/setup representations, codecs, and full simulator composition remain open,
together with the unfinished Action source scans.

The native dependencies remain exactly the inherited named curve-order certificates:

```text
CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt
```

This is local validation of the recorded proof tree, not a claim about hosted CI,
an independent audit, historical priority, or a theorem with all runtime obligations
discharged. The full [checklist](CHECKLIST.md) tracks the remaining extensions.

| Review activity | Status at the proof baseline |
| --- | --- |
| Map claims to experiments, premises, failure observations, and resource scope | Locally checked in this packet |
| Check transitive declarations and named native dependencies | Passed the recorded focused build and direct-pin inventory; preceding full build recorded separately |
| Independent reviewer, reviewed commit, findings, and resolutions | Pending; no independent assessment recorded |

An independent review should focus on whether each advertised claim matches its
experiment, whether auxiliary data and shared state preserve the asserted seed
independence, whether failed prefixes and stopping branches stay visible, and
whether the computational claims charge the actual truncation tail, whether the
application constructor premises and extraction boundary are accurately stated,
and whether future efficiency claims add the required execution-cost proofs.

**Bounded map-scan checkpoint**

The [validation record](review/validation-e3bc4f81.log) covers the exact
map-policy refinements, bounded kernel checker, and adversarial checks. The
[axiom inventory](review/axioms-e3bc4f81.log) contains only the standard Lean
logical axioms. The trust-boundary build passed with 3768 jobs and the regression
build passed with 2566 jobs. Full Action source scans remain in progress.

**Complete inferred-quotient checkpoint**

The [validation record](review/validation-bff126f7.log) covers 64 declarations
across eleven modules, each directly pinned. The
[transitive axiom inventory](review/axioms-bff126f7.log) contains only standard
Lean logical axioms. The complete quotient build passed with 3046 jobs and the
trust-boundary build passed with 3779 jobs. The bound includes actual query and
argument preparation, the full constraint list, domain values, materialization,
and the quotient fold. Public-input/setup representations, encoding, whole
simulator composition, and the Action source scans remain separate work.

The stored-input checkpoint passed its [focused 3,282-job build and both trust boundaries
(3,831 jobs)](review/validation-de8910f0.log). All [68 declarations across five
modules](review/axioms-de8910f0.log) have exactly one direct pin. Only the two
Action-instance-row connection lemmas inherit the existing Pallas certificate;
the other declarations use standard Lean axioms. Materialized public inputs,
setup vectors, key data, and complete bit tapes have checked reader/conversion
costs and exact representation theorems. Whole-simulator composition, transcript
encoding/observation, and the real-prover-and-test PRNG runtime remain open.
