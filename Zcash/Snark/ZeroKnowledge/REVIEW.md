# ZK review packet

Proof baseline: `915317a16740cbe176ae694bf9f3c2e85fa1a418` on `establish-zk` in
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
budgets. A costed simulator implementation, machine running-time bound, and the
resulting PRNG test-class membership proof remain open.

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

[AdviceSourceCertificate.lean](AdviceSourceCertificate.lean) retains the original
instructions and copy tags with their semantic read annotations. Its finite-data
constructor requires equality to the original addresses, reads, and tags. Source
transport changes proof metadata while leaving the stored data directly evaluable.
The [proof-producing elaborator](../../Meta/AdviceSourceCertificate.lean) applies
source equations and support lemmas; its completed certificate is checked by the
kernel. [Adversarial checks](../../Meta/Tests/AdviceSourceCertificate.lean) reject
omitted reads, unavailable reads, and changed source addresses.

[ActionWitnessLoadCertificate.lean](ActionWitnessLoadCertificate.lean) instantiates
that interface for all eleven original instructions in the eight-region loading
stage. Both finite scans are kernel checked at the proved Action placement. This
is a static proof artifact with code generation disabled for expanded kernel-only
source auxiliaries; the original witness constructor remains executable.

[ActionWitnessObservation.lean](ActionWitnessObservation.lean) identifies the
extraction agreement needed for completeness. It retains every witness field and
exactly the 32 auxiliary Merkle readings used by the two 16-layer computations.
Truncating the unused tail preserves the application specification and the
existing honest-prover preconditions. Agreement with the normalized application
observations transfers the constructor's proved preconditions to the extracted
data; that agreement remains to be established for the actual assignment.

The actual Action still needs the complete certified annotation list and both
global checks. Its final witness equations and extracted private data therefore
still need their correctness proofs. The semantic precondition theorem concerns
the normalized application data; it does not assume that the constructor's extractor
already has those observations. Generated gate, lookup, and copy validity, and hence an
application-witness-to-`ActionZkRelation` corollary, remain open.

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

**Input conversion costs**

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
latest proof milestone. Every new mathematical declaration has one direct pin;
the seven metaprogram regression declarations are pinned in their test module.
The new milestone uses only `propext`, `Classical.choice`, and `Quot.sound`, with
no admission or native-evaluation certificate. All 917 modules are covered by
default targets and all 326 endpoint declarations are pinned. The full
[parent](TrustBoundary.lean) and [Action](Action/TrustBoundary.lean) boundaries also
check the earlier milestones.
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
| Check transitive declarations and named native dependencies | Passed the full build and direct-pin inventory |
| Independent reviewer, reviewed commit, findings, and resolutions | Pending; no independent assessment recorded |

An independent review should focus on whether each advertised claim matches its
experiment, whether auxiliary data and shared state preserve the asserted seed
independence, whether failed prefixes and stopping branches stay visible, and
whether the computational claims charge the actual truncation tail, whether the
application constructor premises and extraction boundary are accurately stated,
and whether future efficiency claims add the required execution-cost proofs.
