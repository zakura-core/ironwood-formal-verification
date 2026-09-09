# ZK review packet

Proof baseline: `f4708f711abbd8384b717452fd3e9bd55fb62968` on `establish-zk` in
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
| Application witness construction and simulation | `actionWitnessRows_relation`, `wideActionWitness_simulation_error_bound`, and `storedActionOracleBitWitness_simulation_error_bound` in [ActionWitnessSimulation.lean](ActionWitnessSimulation.lean) | The same real prover on constructed rows, compared with the public-input interactive or counted fixed-bit simulator |
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
  already connected. The [application bridge](ActionWitnessSimulation.lean)
  constructs those rows under `ActionWitnessConstructionConditions`: `ActionSpec`,
  hash definedness, canonical Merkle encodings, and five scalar-hint bounds.
  It no longer requires callers to supply already-satisfying rows or scan results.
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
budgets. The complete [stored-input simulator](StoredActionOracleSimulatorCost.lean)
has a [fixed structural execution-cost bound](StoredActionOracleSimulatorBound.lean)
and [exact law equality](StoredActionOracleRuntime.lean) with the original fixed-bit
simulator. Public initialization, bit packing/reduction, the entire PLONK/IPA
proof, canonical codecs and observation, query replay, and cache programming are
included, with all failure branches retained. Inputs are materialized public
inputs, setup vectors, key trees/layout, bits, and the initial cache; setup/key
generation is outside the supplied-input model. The budget records explicit
primitive operation prices. The real prover's [lookup-prefix construction](LookupSortRowsCost.lean)
now has a complete input-size bound covering sorting, reservations, reverse filling,
and failures. The [lookup and permutation ratio scans](RunningProductCost.lean)
retain every row-provider cost and inherited chunk, including zero denominators.
Their results equal the original computations for every input. Composing those
components with the [actual lookup compression and sorting](PlonkLookupSortCost.lean)
and [lookup-product row constructor](PlonkLookupProductCostBound.lean) now discharges
their complete row-reader costs. This includes original query routing, missing-column
defaults, full row-polynomial preparation and evaluation, expression trees, and
all exceptional inputs. The complete real-prover-and-test runtime needed for PRNG
test-class membership remains open; no machine-code correspondence is asserted.
The [real permutation-row constructor](PlonkPermutationProductCostBound.lean) now
also has a complete bound covering the original packed column/sigma queries,
all identity-name powers, indexed products, and inherited three-chunk scans.
Its exact-result theorem retains every row and zero-factor case.
The [complete stored column runner](PlonkStoredColumnsCost.lean) executes the
original 22-column schedule per Action, retaining earlier masked columns and the
exact offsets of the selected row-mask tape. Its
[combined bound](PlonkStoredColumnsCostBound.lean) includes all constructor work,
materialization, masking, and stored-history reads, including totalized failures.
The [complete stored private material](PlonkStoredMaterialCost.lean) now composes
that column runner with the actual batched pre-IPA decoder. Exact erasure retains
every row mask, both linear-mask coefficients, and all commitment blinds; tape
selection uses only the proved public layout. Its
[combined cost bound](PlonkStoredMaterialCostBound.lean) includes all schedule,
decoding, construction, masking, and stored-history work. The remaining real
polynomial, IPA, and reduction composition still belongs to the open resource item.

The [complete constraint-numerator constructor](PlonkNumeratorCoefficientsCost.lean)
has a [full structural cost bound](PlonkNumeratorCoefficientsBound.lean). It computes
32768 fixed coset evaluations from the actual row readers and stored key, materializes
them once, interpolates their coefficients, and undoes the coset shift. The bound
concerns this stored implementation of the reference function. The
[Action compiler specialization](ActionNumeratorCoefficientsCost.lean) supplies all
domain and degree premises. Its erasure theorem holds for every private row state
and verifier challenge; the internal interpolation domain adds no verifier
challenge exclusion. Stored polynomial arithmetic, root/domain division, and
coefficient-block extraction also have exact-result and size/cost theorems.
Division covers nonzero remainders, and opening-divisor construction preserves the
source's deduplication of repeated points. Whole opening-polynomial, real IPA, and
retry/test composition remain part of the open resource item. The Action
specialization inherits the existing Pallas generator-order native certificate,
which is explicitly named in its direct trust-boundary pin.

The [complete quotient-piece constructor](PlonkQuotientRowsCost.lean) now carries
the original rows through numerator reconstruction, domain division, and all eight
stored pieces. Its [cost bound](PlonkQuotientRowsBound.lean) includes that entire
composition; the [Action compiler corollary](ActionQuotientRowsCost.lean) supplies
the concrete premises. The [private coefficient constructor](PrivatePolynomialCoefficientsCost.lean),
[exact group routing](DenseOpeningGroupCost.lean), and
[stored opening-polynomial folds](DenseOpeningPolynomialCost.lean) retain every
coefficient provider, source-order choice, and arithmetic cost. Generic group
erasure requires that supplied coefficients denote the stated public/private
polynomials; the checked row constructor supplies the private-column identity.
The multi-opening interpolants, real IPA, and complete reduction composition
remain part of the open resource item.

The [full opening material](PlonkOpeningMaterialCost.lean) now constructs all five
polynomials directly from the original public/private rows and stored quotient
pieces, with the original point sets and inherited blinds. Its
[complete bound](PlonkOpeningMaterialBound.lean) includes every coefficient
producer and all group assembly. [Totalized interpolation](LagrangePolynomialTotal.lean)
retains coincident query positions in the interpolant; divisor construction uses
the source's separate deduplication rule. The
[complete stored multi-opening polynomial](DenseMultiopenFinalCost.lean) has exact
source erasure and a [full cost bound](DenseMultiopenFinalBound.lean), including
the constructed group quotients and final fold. Complete real IPA execution and
prover/retry/test resource composition remain open. These new generic results use
only the standard logical axioms and introduce no native certificate.

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
[read](ActionAdviceReadPlan.lean) and [alias](ActionAdviceSourceAliasCheck.lean)
scans now instantiate this mechanism for all 18,403 original instructions.

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

The complete [source certificate](ActionAdviceSourceCertificate.lean) now
discharges that premise for the actual generated assignment, using the successful
global advice scans and the original semantic copy and read certificates.
[CompiledGateCompleteness.lean](CompiledGateCompleteness.lean)
derives all compiled gates from the operation equations, positive selector
degree, and an explicit finite activation-coverage condition. Source identities
retain gate names as well as selector indices; the actual coverage scans are now
checked below. [ActionQueryRows.lean](ActionQueryRows.lean) interprets the generated
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
activation-coverage checks. [ActionGateActivationCoverage.lean](ActionGateActivationCoverage.lean)
and [ActionLookupActivationCoverage.lean](ActionLookupActivationCoverage.lean) now
discharge both coverage premises on the complete original source. All 55 configured
gates and three lookup masters retain their exact required rows. The
[gate-index equivalence](GateIndexedCoverage.lean) holds for every input list,
including unknown names, shared selectors, and wrong rows.
[ActionWitnessSimulation.lean](ActionWitnessSimulation.lean) combines those checks
with the complete source witness equations and original completeness theorem.
`actionWitnessRows_relation` constructs `ActionZkRelation` directly from
`ActionWitnessConstructionConditions`; it assumes neither valid circuit rows nor
successful scan results. Those construction conditions still require `ActionSpec`,
defined hashes, canonical Merkle encodings, and the five scalar-hint bounds.
The application corollaries instantiate the interactive and captured-setup bounds
and the complete one-attempt oracle comparison. The stored-simulator corollary
uses the exact counted implementation with the complete runtime and law theorems.
The interactive bound is `plonkSimulationErrorBound m`; the fixed-bit oracle bound
is `plonkBitSimulationErrorBound m q`. Neither is a perfect-ZK claim.

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

[PlonkJointSimulatorCost.lean](PlonkJointSimulatorCost.lean) computes the complete
materialized mask, builds its stored readers, computes the actual inferred
quotient and public opening, and constructs every IPA output.
`plonkJointSimulatorCosted_result` identifies the exact finite observation of
`plonkJointSimulatorFromCoins`, using `plonkVerifierHx` internally. The
[complete cost theorem](PlonkJointSimulatorCostBound.lean) composes those same
algorithms. Generated mask-reader dimensions and access bounds follow from the
constructor; no expected-quotient or preparation callback is left unpriced.
The [composite budget](PlonkJointSimulatorBudget.lean) retains the actual key
trees/layout, all supplied reads, both field/group primitive price records, and
every preparation stage. It applies to exceptional challenges and zero defaults.

[StoredActionJointCost.lean](StoredActionJointCost.lean) supplies the actual Action
instance rows and materialized setup readers. Its [cost theorem](StoredActionJointCostBound.lean)
discharges every public-row, fixed/sigma, and generator access premise using the
concrete input and setup sizes. The common input envelope is
`25m + R_coin + 2R_read + 4200`; it includes the original ten public fields and
the 2048/29/15 setup dimensions. Remaining coin-reader premises concern the
challenge and private-tape producers. Proof-field routing, encoding, and the
oracle observer remain to be composed with those producers and the counted cache.

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
The [bit-driven joint simulator](StoredActionTapeJointCost.lean) now composes
the complete tape producer with all algebraic work. Its erasure theorem retains
the original tape split, challenge values, and private coins. The
[fixed runtime envelope](StoredActionTapeJointBound.lean) has no reader-price
premises and does not depend on sampled values: the exact stored challenge-read
prices follow from their valid positions. The Action input-read envelope is
`553m + 4R_read + 4457`. The [complete bit-to-transcript construction](StoredActionTapeTraceCost.lean)
now includes original proof routing and scheduling, with a
[fixed cost envelope](StoredActionTapeTraceBound.lean). The canonical observer
and raw reply prefix also have complete counted implementations. Public
initialization, oracle replay, and cache programming still need to compose into
`actionOracleSimulatorFromBits`. A PRNG reduction
executes the real prover and the supplied view test, so its admissibility needs
those runtime bounds in addition to simulator efficiency.

**Input conversion costs**

[StoredBitTapeCost.lean](StoredBitTapeCost.lean) reads materialized Boolean lists
with complete traversal costs and charges construction of each word/bit index.
Its raw and reduced materializers are proved equal to every entry of the existing
fixed-tape conversion. For `N` words, `L` stored bits, and primitive read price `R`,
raw conversion costs at most `N * (512 * (2L + R + 4) + 264195) + N^2 + 1`;
direct field conversion replaces `264195` by `264194`. The bound covers the entire
converted output.

[PlonkStoredTapeCost.lean](PlonkStoredTapeCost.lean) composes both conversions
and the exact challenge/private-coin split. The raw reply prefix and reduced
challenge values are functions of the same original bits; no independence is
introduced between them. [PlonkStoredTapeBound.lean](PlonkStoredTapeBound.lean)
adds all eager scalar reads and derives every later indexed reader's bound from
the generated field-list length. Its common bound is `4N + 2R + 25`, including
both field reads in each IPA-round coin pair. Its connection to algebraic
simulation is now proved above; proof fields and the oracle observer remain.

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
| Check transitive declarations and named native dependencies | Passed the complete 4,629-job build, repository guards, and separate direct-pin inventories |
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

The complete algebraic-simulator checkpoint passed the [3,073-job exact-result
build, 3,081-job bound build, 3,321-job stored Action build, and 3,839-job trust
boundaries](review/validation-ba0159ec.log). All [23 declarations across eight
modules](review/axioms-ba0159ec.log) have direct pins and a separate transitive
inventory. The stored Action result theorem alone inherits the existing Pallas
certificate; all other new declarations use standard Lean axioms. Fixed-bit
routing, proof-field routing, codecs, and oracle observation remain to be composed.

The complete tape-production checkpoint passed [both trust boundaries with 3,844
jobs](review/validation-454c38c8.log). Its [24 declarations across five
modules](review/axioms-454c38c8.log) have exact direct pins and a separate transitive
inventory, using only standard Lean axioms. The raw-response prefix and every
private-coin slot are connected to the existing bit-tape split, and all production
and indexed-read costs are included. The joint-simulator, proof-field, codec,
and oracle-observer composition remains the next runtime layer.

The bit-driven joint-simulator checkpoint passed its [3,344-job result/bound
build, 3,346-job fixed-envelope build, and both trust boundaries with 3,848
jobs](review/validation-a5ad741f.log). All [15 declarations across four
modules](review/axioms-a5ad741f.log) have exact direct pins and a separate transitive
inventory. Only the complete Action erasure theorem inherits the existing Pallas
certificate. The cost envelope covers every input tape without sampled-value or
reader-price premises. Proof-field routing, codecs, and oracle observation are
still separate composition work.

The actual scalar, compressed-point, affine-point, and transcript encoders now
have counted implementations with exact representation theorems. The 25 new
declarations use only standard Lean logical axioms. The original proof codec's
identity rejection and every transcript tag and byte are retained. Connecting
these producers to the complete message schedule and oracle observation remains.

The canonical-encoding checkpoint passed its [three focused builds and the
3,799-job trust-boundary build](review/validation-45f586ac.log). The
[25-declaration inventory](review/axioms-45f586ac.log) has exact direct pins and
only standard Lean logical axioms. These codec results preserve the actual
proof and transcript formats, including the point codec's identity rejection.

The complete original Action source certificates now preserve all 18,403 advice
instructions, 4,058 gate activation entries, and 2,424 lookup activation entries.
Their 14 declarations are directly pinned and have a separate transitive axiom
inventory. They inherit the existing Pallas curve-order certificate, with no new
axiom or native-evaluation certificate. Full read/write scans and activation
coverage remain separate checks on this certified original data.

The original-source checkpoint passed its [three focused builds and both trust
boundaries with 3,855 jobs](review/validation-6c80818e.log). Its
[14-declaration inventory](review/axioms-6c80818e.log) records only standard Lean
logical axioms and the existing named Pallas dependency. These certificates
preserve the original data; read/alias safety and activation coverage are checked
separately before the application-level simulation corollaries can use them.

The read-checker normalization now factors source equations through pure placed
addresses before constructing dependent decision proofs. The exact transition
identity is in [AdviceReadAddressScan.lean](AdviceReadAddressScan.lean), and the
[regressions](../../Meta/Tests/AdviceMapScan.lean) retain opaque source data while
checking both success and rejection. The original Action entries that previously
blocked normalization now pass. The complete global scans are still running.

The original-source normalization checkpoint passed its [focused checks,
regressions, and 3,802-job trust-boundary build](review/validation-159eb4be.log).
The [ten-declaration inventory](review/axioms-159eb4be.log) uses only standard
Lean logical axioms. The original two blocked source entries now check without
changing either policy; the full source-order scans remain the application gate.

The complete proof-routing and transcript-construction checkpoint covers
68 declarations across nine modules. [Routing](RoutedProofCost.lean) preserves
all original proof fields, and [record preparation](ProofRecordProducerCost.lean)
is retained in every used scalar reader. The
[complete schedule](TranscriptScheduleCost.lean) agrees with the original verifier
order. Its [eleven-round bound](TranscriptScheduleBound.lean) is
`8m^2 + (72m + 85)R + 1300m + 2200`, under the explicit complete-producer bound
`R`. It includes every optional claim and both final responses. The separate
transitive inventory uses only standard Lean logical axioms. Stored-joint,
canonical observer, and oracle replay composition remain separate checkpoints.

The complete proof-routing/schedule checkpoint passed its [nine focused builds
and 3,809-job trust-boundary build](review/validation-af86fb24.log). The
[68-declaration inventory](review/axioms-af86fb24.log) has exact direct pins and
only standard Lean logical axioms. Whole-simulator composition and observation
remain separate runtime obligations.

The complete stored-bit transcript and observer checkpoint adds 58 declarations
across sixteen modules. [Exact tape-to-transcript erasure](StoredActionTapeTraceCost.lean)
and the [fixed envelope](StoredActionTapeTraceBound.lean) retain complete bit,
joint, proof-preparation, and schedule costs. The canonical observer and oracle
reports preserve original codecs and abort checks. Raw reply reads expose only
the declared public prefix; their field reductions agree with the same prepared
challenge record. The separate axiom inventory finds only standard Lean logical
axioms and the existing named Pallas curve-order dependency in three Action
theorems. Full public initialization, oracle replay, and cache composition remain.

The stored-bit transcript and canonical-observer checkpoint passed its [sixteen
focused builds and both trust boundaries with 3,881 jobs](review/validation-059f0df7.log).
The [58-declaration inventory](review/axioms-059f0df7.log) records exact direct pins
and only the existing named Pallas native dependency in three Action theorems.
Whole-oracle composition, application source checks, concrete PRNG resource
membership, and independent review remain separate work.


The complete runtime checkpoint composes public initialization, the stored bit
producer, the full Action PLONK/IPA proof, canonical observation, exact query and
raw-reply replay, and cache programming. The exact-result theorem
`storedActionOracleSimulatorCosted_result` in
[StoredActionOracleSimulatorCost.lean](StoredActionOracleSimulatorCost.lean)
recovers `actionOracleSimulatorFromBits` with the actual Action key and codecs.
[StoredActionOracleSimulatorBound.lean](StoredActionOracleSimulatorBound.lean)
proves a fixed total budget for every full input tape, including abort and
programming-conflict paths. It is a sum of initialization, complete view,
programming, and composition costs; generated reader bounds are derived inside
the proof. The prior cache contributes at most
`22 * ((q + 22) * (9490m + 14207) + 4) + 2` for programming.

[StoredActionOracleRuntime.lean](StoredActionOracleRuntime.lean) erases the counter
under the original uniform bit law, proves equality with `actionOracleBitSimulator`,
and transfers its two-sided `plonkBitSimulationErrorBound m q` theorem. The bound
uses explicit primitive prices and materialized inputs; setup/key generation and
compiler or machine-code correspondence are outside this cost model. Runtime of
the real-prover-and-test reduction remains necessary to instantiate its PRNG
admissibility premise. Independent review is still pending.

The complete runtime milestone passed [all nine focused builds and both trust
boundaries with 3,890 jobs](review/validation-fcb1d6a6.log). The
[25-declaration inventory](review/axioms-fcb1d6a6.log) records exact direct pins and
only standard Lean logical axioms plus the existing named Pallas/Vesta dependencies.
All repository guards and local Markdown links passed. This milestone closes the
complete simulator composition and structural runtime items; it does not close
the application witness, concrete PRNG reduction, or independent review items.

The [alias normalization checkpoint](review/validation-fee23404.log) keeps scalar-IR
simplification on entry metadata, before the original map policy. All regressions
passed, including success and rejection after 512 earlier assignments. Its
[five-declaration inventory](review/axioms-fee23404.log) uses only standard Lean
logical axioms. The original blocked source entries also pass; the full read and
alias scans have separate module boundaries so their certificates can be cached
independently. Complete Action source checks remain prerequisites to the
application witness corollaries.

The [complete activation-coverage milestone](review/validation-4ccde259.log) passed
for all 55 configured Action gates and three lookup masters, using every original
source entry. Its [51-declaration inventory](review/axioms-4ccde259.log) records exact
direct pins; only the four Action theorems add the existing named Pallas dependency
to standard Lean logical axioms. Both trust boundaries and all repository guards
passed. The indexed scan is proved equal to the original for all inputs and retains
all rejection cases. The complete advice scans and application witness corollaries
remain the circuit-construction work.

The [complete application witness milestone](review/validation-2872c72f.log) passed
the full `lake build --wfail` with 4,629 jobs, including both trust boundaries and
the original certificate regressions. The global read and alias scans each
checked all 18,403 original entries; the application corollaries use their actual
source certificate, with no supplied successful-check or row-validity premise.
All [nine new declarations](review/axioms-2872c72f.log) have direct pins and a
separate transitive inventory. The five source/row theorems retain the existing
Pallas owner; the four simulation corollaries additionally retain the existing
Vesta owner. No axiom, admission, or native-evaluation certificate was added.
Repository guards pass with 331 endpoints and all 1,092 workspace modules covered.
The application contract remains `ActionWitnessConstructionConditions`. The
complete counted simulator and its statistical law are also covered by this full
build. Concrete PRNG reduction resource admissibility and independent review are
the remaining unchecked extensions.

The [real-prover lookup and product milestone](review/validation-b571d36a.log)
passed its focused 2,766-job build and both trust boundaries with 3,907 jobs.
All [57 declarations across six modules](review/axioms-b571d36a.log) have exactly
one direct pin and use only standard Lean logical axioms. The bounds include
sorting failures and zero-denominator product paths. Whole real-prover reduction
admissibility and independent review remain open.

The [complete real lookup-construction milestone](review/validation-907fe7f2.log)
passed its 3,050-job focused build and 3,843-job trust-boundary build. Its
[34 declarations across ten modules](review/axioms-907fe7f2.log) have exact direct
pins and only standard Lean logical dependencies. The result covers complete
lookup sorting and product rows, with all original query and expression costs.

The [complete real permutation-construction milestone](review/validation-2bcc329a.log)
passed its 3,054-job focused build and 3,854-job trust-boundary build. All
[33 declarations across eleven modules](review/axioms-2bcc329a.log) have exact direct
pins and only standard Lean logical dependencies. Its combined bound includes
original packed-pair queries, identity-name powers, and every inherited chunk.

The [complete stored-column milestone](review/validation-a3d50916.log) passed its
3,084-job focused build and 3,871-job trust-boundary build. All
[51 declarations across seventeen modules](review/axioms-a3d50916.log) have exact
direct pins and only standard Lean logical dependencies. The result and bound
cover the full original column schedule on the identical selected row-mask tape.

The [actual-tape private-material milestone](review/validation-57e86f0d.log) passed
its 3,107-job focused build, 3,884-job trust-boundary build, and all repository
guards. Its [54 declarations across thirteen modules](review/axioms-57e86f0d.log)
have exact direct pins and only standard Lean logical dependencies. This closes
tape decoding and complete private-state construction within the real-prover
resource proof; polynomial, IPA, and reduction composition remain separate work.

The [Action numerator milestone](review/validation-abe0c7e0.log) passed the
warning-as-error trust-boundary build and a separate axiom inventory of
[115 declarations across twenty-one modules](review/axioms-abe0c7e0.log).
Source guards ran against an archive of that exact proof commit. The Action
specialization retains its explicitly pinned inherited Pallas generator-order
certificate. This records focused validation; whole real-prover/reduction resource
closure and independent review remain open.

The [quotient and opening-polynomial checkpoint](review/validation-d8c0b95d.log)
passed the focused 3,919-job trust-boundary build and a separate inventory of
[75 declarations across fourteen modules](review/axioms-d8c0b95d.log). All have one
direct pin; the Action specialization retains the existing Pallas generator-order
native owner. The exact committed tree passes the 331-endpoint and 1,184-module
coverage checks, along with the remaining repository guards. This is focused
validation; the last complete workspace build remains the earlier recorded baseline.

The complete opening-material checkpoint passes the [focused 3,940-job trust-boundary build](review/validation-531dc5f7.log), with [85 separately inventoried declarations](review/axioms-531dc5f7.log) across 21 modules. All use only the standard logical axioms. This is component validation; complete real-prover resource admissibility and independent review remain open.

The [counted real IPA](HonestIpaTapeCost.lean) now preserves the complete original tape-driven transcript and has a [full materialization bound](HonestIpaBound.lean). Its input prices cover every coefficient, public input, and tape read. The statement includes zero challenges and retains the supplied claimed value. PLONK preparation and the complete prover/retry/test resource composition still require composition with this component.

The complete real-IPA checkpoint passes the [focused 3,955-job trust-boundary build](review/validation-eeb9dc07.log), with [74 separately inventoried declarations](review/axioms-eeb9dc07.log) across 15 modules. Their transitive dependencies use only the standard logical axioms. The complete prover/retry/test resource bound and independent review remain open.

The [complete real joint computation](HonestJointRowsSource.lean) now has exact
source erasure and a [full cost bound](HonestJointRowsBound.lean), from original
row readers and stored quotient pieces through all PLONK commitments and
observations, the complete multi-opening data, and every real IPA output.
The [prepared IPA connection](PreparedHonestIpaSource.lean) preserves both the
original commitment and verifier-reconstructed claimed value without a challenge
exclusion. Generated dimensions are checked. Complete private-tape, observer,
retry, and test composition remains part of the open PRNG resource item.

The real joint-prover checkpoint passes the [focused 3,979-job trust-boundary build](review/validation-f4708f71.log), with [76 separately inventoried declarations](review/axioms-f4708f71.log) across 24 modules. All use only the standard logical axioms. The exact committed tree passes the 331-endpoint and 1,244-module coverage checks and the remaining repository guards. Complete real-prover/retry/test resource composition and independent review remain open.

The [complete real private-tape computation](HonestStoredMaterialSource.lean) now
includes material generation, the actual numerator and quotient pieces, all
opening data, commitments, evaluations, and the original IPA suffix. Its
[combined bound](HonestStoredMaterialBound.lean) discharges generated row widths
and every stored reader. The [Action bit-tape adapter](StoredActionHonestTapeJoint.lean)
preserves the original private sample order and correlated raw/field views,
with [a fixed cost independent of sampled values](StoredActionHonestTapeBound.lean).
The [complete canonical view](StoredActionHonestOracleViewCost.lean) has both
source equality and a [full structural bound](StoredActionHonestOracleViewBound.lean),
including actual codecs, raw replies, and failure checks. This view uses
independent raw replies; the online cache, retry, and distinguishing-test
composition remains part of the PRNG resource obligation.
