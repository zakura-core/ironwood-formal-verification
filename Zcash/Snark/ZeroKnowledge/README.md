# Zero-knowledge formalization

This development starts from the [pinned prover description](https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md),
alongside the existing Lean protocol, on Ironwood base
`ad4a6ad8f75a64368bae4186006480410a687cce`. The proof target is the specified honest-prover
algorithm. Whole-program Rust equivalence is a separate claim, not a prerequisite for
this protocol theorem.

The description labels its source `sensei at 56a7de7`, which resolves to
[Bento commit `56a7de7474da3b86fa475f01400edadfd8af4cb6`](https://github.com/tachyon-zcash/bento/commit/56a7de7474da3b86fa475f01400edadfd8af4cb6).
The [Sensei crate](https://github.com/tachyon-zcash/bento/tree/56a7de7474da3b86fa475f01400edadfd8af4cb6/crates/sensei)
is present at that revision.

The [ZK checklist](CHECKLIST.md) records the completed interactive theorem and
optional assumption instantiations, Fiat–Shamir proofs, and unlimited-retry targets.
The [review packet](REVIEW.md) maps the current claims to exact experiments,
assumptions, bounds, and validation evidence; independent review remains pending.
The [Action instantiation](ActionInstantiation.lean) now packages original gate,
lookup, and copy validity into one relation and specializes the full encoded
comparison to a named captured URS. The simulator uses only public inputs and
setup parameters. The captured-setup corollary supplies the eleven-round and
nonidentity proofs internally; it does not assert an application witness constructor.
The [application witness constructor](ActionWitnessRows.lean) now supplies a
separate, computable conversion to original advice rows using the actual fixed
programs and region placement. Its [input contract](ActionWitnessConditions.lean)
starts from `ActionSpec`, records hash definedness and canonical encodings, and
requires each scalar's Nat representative to fit the existing one-field hint.
[Hint decoding](ActionWitnessHints.lean), [scalar windows](ActionWitnessHintWindows.lean),
and [canonical Merkle folds](CanonicalMerklePath.lean) are checked. The interpreter
preserves public inputs and reconstructs the same canonical compiler environment.
The [source witness-equation bridge](CompiledFixedWitnesses.lean) now discharges
fixed writes and table contents from the compiled key. A
[checked dependency collector](WitnessProgramSupport.lean) covers the complete
structured witness IR and its [builder forms](WitnessBuilderSupport.lean).
The [trace theorem](AdviceWitnessTrace.lean) now allows repeated writes while
preserving every previously established value. Its [alias checker](AdviceAliasPlan.lean)
requires semantic copy certificates for every annotated program. The original
[Action multiplication region](ActionMulNativeCopies.lean) has such native-copy
certificates, including its actual shared base columns. The
[complete source-routing theorem](ActionNativeRouting.lean) now proves every
collected annotation's evaluator semantics through the original Action schedule.
The [function-support interface](WitnessFunctionSupport.lean) now certifies the
original native witness functions for Poseidon, incomplete and fixed-base
multiplication, note commitment and canonicity, CommitIvk, Sinsemilla, and Merkle
layers. Nested callback requirements remain explicit. The
[fixed Action hint programs](ActionHintReadSupport.lean), including scalar windows
and Merkle swap callbacks, read no advice cells. The
[certified annotation checker](AdviceSupportPlan.lean) combines these semantic
certificates with a finite read-availability check and exact source erasure.
The [address projection](AdviceAliasAddressPlan.lean) discards witness function
bodies from the alias calculation. The [finite-map alias check](AdviceAliasMapPlan.lean)
and [finite-map read check](AdviceSupportMapPlan.lean) preserve every result of
the original checks and feed the same compiler witness-equation theorem.
The [source certificate](AdviceSourceCertificate.lean) retains original copy tags
beside the read annotations. Its finite-data constructor requires proved equality
to the original addresses, reads, and tags; it keeps those data directly evaluable.
The original [witness-loading stage](ActionWitnessLoadCertificate.lean) has a
complete eleven-instruction certificate and successful kernel-checked read and
alias scans. The original [value-commitment stage](ActionValueWitnessCertificate.lean)
also has a complete source certificate covering 1,083 instructions for arbitrary
stage inputs, including both multiplications and the final addition. Named
structured witness wrappers use the general IR support theorem; unrecognized
native callbacks remain rejected. These static proof artifacts are separate from
the executable witness constructor.
Applying it to the Action still requires the complete annotation list and the
global alias and read-plan checks.
The [extraction theorem](ActionWitnessExtraction.lean) now recovers all private
readings needed by completeness from the original witness equations: eight
fields, six points, five scalar/window pairs, and 32 Merkle readings. The
[reading agreement](ActionWitnessReadings.lean) transfers the normalized
application's preconditions, and [ActionWitnessCompleteness.lean](ActionWitnessCompleteness.lean)
applies the original completeness theorem with the preserved public inputs.
This connection still requires the full source certificate to establish the
witness equations. It does not require equality of unused decomposition exports.
The [gate compiler bridge](CompiledGateCompleteness.lean) now derives verifier
polynomials from the original equations under explicit activation coverage.
[Actual query-row interpretation](ActionQueryRows.lean) and
[inactive-row handling](InactiveGateCompleteness.lean) retain the cyclic boundary
behavior. The [copy compiler bridge](CopySourceCompleteness.lean) preserves every
ordinary and deferred constant equation, and [ActionCopyValues.lean](ActionCopyValues.lean)
identifies those values with the prover's actual packed permutation cells.
[ActionLookupValues.lean](ActionLookupValues.lean) derives paired lookup tuples
through the exact query compiler, including the actual fallback table values on
inactive rows. [ActionGateValues.lean](ActionGateValues.lean) and
[ActionRowRelations.lean](ActionRowRelations.lean) retain the gate and lookup
equations through the reference-key shape. The complete witness-equation scans
and actual gate and lookup activation coverage remain necessary before the
constructor establishes `ActionZkRelation`.
The [raw-source refinement](ActionRandomnessSource.lean) proves exact agreement
between uniform 512-bit private tapes and the existing wide-reduced reference law.
Replacing that entire source by a distribution within `eta` adds `eta` to the
statistical simulation bound. The [seeded-tape reduction](ActionPrng.lean) instead
assumes a distinguishing bound only for its actual Boolean-output reduction,
and proves the same additive comparison for a probabilistic view test. It makes
the generator and seed law explicit and covers one attempt. The
[PRNG security game](PrngSecurity.lean) now specifies a uniform bit seed,
independent retained auxiliary data, the complete output type, and an admissible
class of randomized Boolean tests. The [Action game reduction](ActionPrngSecurity.lean)
proves exact agreement with the actual distinguishing experiment and a bound of
`epsilon(m) + eta` under that security assumption. The complete prover-and-test
reduction must belong to the supplied class. A concrete generator security proof
and a runtime proof establishing that membership remain separate obligations.

The [typed Action comparison](ActionTyped.lean) exposes the same reference law before
the attempt observer. [Raw digest recovery](ActionDigest.lean) now proves the same
`epsilon(m)` bound when the view also includes every 512-bit challenge response.
The simulator samples uniformly from the exact preimage of each field challenge;
the [joint recovery law](DigestTape.lean) introduces no additional sampling-bias
term. [Transcript bytes](TranscriptBytes.lean) encode scalars, affine point
coordinates, and challenge markers injectively, and [the hash boundary](ByteFiatShamir.lean)
includes the specified personalization and wide reduction. These results concern
the full joint raw-response distribution, which is used in the oracle comparison below.
The [cached oracle](CachedOracle.lean) now has exact independent-tape semantics,
with one stored answer for each address. [Conflict-checked programming](OracleProgrammingBias.lean)
preserves those answers and gives a generic two-sided comparison whose error is
the programming-conflict probability, including for privately randomized oracle
computations.

The [Fiat–Shamir capstone](ActionFiatShamir.lean) proves single-attempt statistical
simulation in a programmable classical random oracle. For `m > 0` Actions and
at most `q_pre` oracle queries before the proof, its two-sided error is
`epsilon(m) + q_pre / p`. The [adversary experiment](ActionOracleAdversary.lean)
permits adaptive selection of the public inputs and a valid witness, arbitrary
retained auxiliary state, and further adaptive queries after the attempt. The
simulator receives the public request, auxiliary state, and cache; the selected
witness is erased. The comparison includes the complete observed attempt and
the final cache, including failed prefixes and explicit programming failure.
The setup remains fixed, with eleven rounds and nonidentity `W`, and private
prover bits are fresh and independent of the adversary's preceding execution.

The [causal oracle driver](PlonkOracle.lean) runs the same full reference prover
and abort checks. [Every query prefix](PlonkQuerySchedule.lean) agrees with the
existing verifier's eleven pre-IPA squeezes and all eleven IPA rounds; the Action
corollary includes the compiler's public instance commitments. The
[conflict bound](ActionOracleConflicts.lean) uses the simulator's exactly uniform
first advice commitment, which occurs in every prover query. Each prior address
can name at most one such point, while internal query addresses are distinct.
The comparison therefore charges `q_pre / p` once and preserves the existing
`epsilon(m)` without another wide-reduction term.

The [executable simulator](ActionOracleSimulator.lean) has exactly the same law:
it samples 22 raw 512-bit challenge words, uses
[132m + 36 uniform field draws](PlonkSimulatorTape.lean), and runs the computable
public PLONK and IPA simulator. The real prover still uses its original
`148m + 46` wide-reduced private fields. Both experiments have at most
[`q_pre + 22 + q_post` cache entries](ActionOracleResources.lean). These are
checked sampling and oracle-resource bounds; machine-instruction and bit-sampler
running times are not formalized here. The hash model uses the existing Lean
protocol's total public-prefix coordinate encoding. Relating concrete BLAKE2b
to the random oracle remains a cryptographic modeling assumption. This theorem
covers one attempt; its finite and unlimited shared-oracle retry extensions are
described below.

The [fixed-bit simulator](ActionOracleBits.lean) supplies a second implementation
that also wide-reduces its private fields. It takes `512 * (132m + 58)` independent
uniform bits: 22 words for raw challenges and `132m + 36` words for its field
draws. [Explicit little-endian packing](RawBits.lean) and
[raw-tape reduction](RawFieldTape.lean) prove its exact distribution, with no
rejection sampling. Its own reductions add `(132m + 36) * delta` to the earlier
comparison; the ideal-field simulator and its sharper bound remain available.
The [bit-tape Fiat–Shamir theorem](ActionFiatShamirBits.lean) therefore gives

```text
epsilon_bits(m, q_pre) = (42882m + 4113 + q_pre) / p + (280m + 106) delta
                      < m * 2^-238 + q_pre / p,  for m >= 1.
```

The [binary inequality](OracleBitBounds.lean) is kernel checked. This bound
covers the same adaptive before/proof/after experiment and final oracle cache,
including programming failure. The `280m + 106` coefficient counts terms in the
distributional comparison; it is not either program's tape length. The simulator
uses a fixed number of input bits and at most the same `q_pre + 22 + q_post`
cache entries. A machine-instruction running-time bound is still separate.

The [costed byte comparator](ByteEqualityCost.lean),
[cache lookup](OracleCacheCost.lean), and
[conflict-checked programmer](OracleProgrammingCost.lean) now retain structural
execution counters with exact erasure to the existing results. Failed programming
keeps the cost of the preceding work. For materialized query logs, the
[Action cache-phase theorem](ActionCacheCost.lean) derives
`22 * ((q + 22) * (9490m + 14207) + 4) + 2` units from the original 22-query
schedule and its [linear transcript-size bound](PlonkTranscriptSize.lean).
Here `q` is the initial cache length and `m` is the Action count. The units count
byte comparisons, structural case tests, and cache-cell construction. The
surrounding proof construction, codecs, and observer are included in the complete
composition below.
The counted [bit packer](RawBitPackingCost.lean) and
[wide reducer](WideBitReductionCost.lean) now reproduce exactly the existing
raw-word and field-tape conversions. Each 512-bit word costs at most
`512R + 264193` structural units for a reader with access bound `R`, including
successor-index adapters and bounded-width arithmetic. The
[stored-tape implementation](StoredBitTapeCost.lean) additionally charges every
bit-list traversal and word-index calculation, and materializes the complete raw
or reduced tape with a polynomial bound in its length. Its erasure is the same
fixed-tape conversion. The [complete tape producer](PlonkStoredTapeCost.lean)
also recovers the original challenge/private split and every private-coin position.
Raw replies and reduced fields come from the same bits, preserving their correlation.
Its [bound](PlonkStoredTapeBound.lean) includes both packing passes, eager scalar
loads, and full subsequent indexed reads.

Concrete [row readers](StoredRowsCost.lean), [Action input serialization](ActionPublicInputCost.lean),
[stored setup vectors](StoredPlonkSetupCost.lean), and [stored key readers](StoredPlonkKeyCost.lean)
now derive access bounds from the actual materialized inputs. Their representation
theorems preserve the original public rows, generator vector, and key trees/layout.
These are supplied-input bounds; they do not price setup generation.

The [complete counted joint simulator](PlonkJointSimulatorCost.lean) now composes
the materialized PLONK mask, stored readers, complete quotient and public opening,
and every IPA output. Its exact-erasure theorem preserves the original joint
simulator at all challenge values. The [total bound](PlonkJointSimulatorCostBound.lean)
retains every preparation stage and derives the generated readers' sizes and
access costs from the mask constructor. The [stored Action adapter](StoredActionJointCost.lean)
and its [bound](StoredActionJointCostBound.lean) instantiate public rows and setup
accesses using their concrete representations. The [bit-driven composition](StoredActionTapeJointCost.lean)
now connects the complete bit producer to this joint computation. Its
[fixed bound](StoredActionTapeJointBound.lean) depends only on input sizes, stored
key structure, and primitive operation prices, for every possible bit tape.
The actual [scalar codec](ScalarEncodingCost.lean), [point codecs](PointEncodingCost.lean),
and [transcript encoder](TranscriptEncodingCost.lean) now have exact-result and
complete cost theorems. They preserve canonical bytes and identity rejection.
The [complete stored-bit transcript](StoredActionTapeTraceCost.lean) now composes
proof routing and message scheduling, with a [fixed cost envelope](StoredActionTapeTraceBound.lean).
The [canonical observer](CanonicalObserverCost.lean) retains the original bytes,
received challenges, and abort checks. The [complete stored-input simulator](StoredActionOracleSimulatorCost.lean)
now composes public instance commitments, the bit-driven proof, every query and
raw reply, canonical observation, and conflict-checked cache programming. Erasing
its counter gives exactly `actionOracleSimulatorFromBits` for the actual Action
compiler key and original codecs, including all failure branches.

The [complete runtime bound](StoredActionOracleSimulatorBound.lean) applies to
every complete bit tape. It depends on the Action count, prior cache length,
stored bit length and key structure, and explicit field/group, equality, read,
and structural operation prices. Setup/key generation is outside this model of
supplied inputs. The [distribution theorem](StoredActionOracleRuntime.lean) proves
that this counted implementation has the existing fixed-bit simulator's law and
two-sided statistical error bound. These are structural execution costs;
compiler and machine-code correspondence and the real-prover-and-test PRNG
resource bound remain separate.

The [counted IPA simulator](IpaSimulatorCost.lean) now constructs and materializes
every round point, the mask commitment, and both scalar responses. Its erasure
theorem gives exactly the existing simulator's complete finite observation;
its cost bound retains the supplied public-input and coin-reader costs, both
[public folds](PublicFoldCost.lean), the [scalar case test](IpaScalarCost.lean),
and all [IPA arithmetic](IpaArithmeticCost.lean). It applies at exceptional
challenge values too. Materialization pays for all output fields before any
later encoder failure; shared work may be conservatively charged more than once.

Further counted components cover the actual [expression AST](ExpressionCost.lean),
[lookup compression](ExpressionCompressionCost.lean), all five
[lookup constraints](LookupExpressionsCost.lean), and both
[permutation-chunk product folds](PermutationChunkCost.lean). The complete
[permutation calculation](PermutationExpressionsCost.lean) includes its initial,
final, and inter-set constraints. [Constraint assembly](ConstraintAssemblyCost.lean)
and [collection across Actions](ConstraintCollectionCost.lean) preserve the entire
ordered constraint list and retain input-provider costs and output construction.
The [Lagrange basis calculation](LagrangeBasisCost.lean), including signed powers,
and the [quotient evaluation fold](QuotientEvaluationCost.lean) have matching
counted implementations. [Scalar query routing](QueryRoutingCost.lean) preserves
the original zero defaults and charges the selected reader.
The [full Lagrange interpolant](LagrangeEvaluationCost.lean) and
[multi-opening scalar calculation](MultiopenEvaluationCost.lean) also have exact
costed implementations. A [direct commitment/scalar fold](MultiopenCombinationCost.lean)
is proved equal to evaluating the verifier's symbolic MSM combination.
[Private-column routing](PrivateColumnRoutingCost.lean) counts construction and
search of the actual schedule, and [entry routing](CommitmentEntryCost.lean)
preserves every emitted slot while retaining the complete selected-reader cost.
[Polynomial evaluation](PolynomialArithmeticCost.lean) loads the actual canonical
coefficient array and proves its counted Horner result equals the existing
evaluator. [Coefficient commitments and claim folds](CommitmentArithmeticCost.lean)
retain every generator, coefficient, and challenge access.
[Public row coefficients](RowCoefficientCost.lean) are also constructed by a
counted inverse DFT and proved equal to the canonical interpolant's coefficients.
The [row evaluation and commitment algorithms](RowPolynomialCost.lean) include
that preparation and retain the complete supplied row-provider costs.
The [PLONK mask simulator](PlonkMaskSimulatorCost.lean) now has a complete
materialized cost bound. [Private opening evaluations](PrivateOpeningEvaluationCost.lean)
include group construction, column routing, and Horner arithmetic;
[public opening claims](PublicOpeningClaimsCost.lean) also include their actual
query-table routing and public polynomial preparation.
The [complete public opening](PublicOpeningCost.lean) now joins all five
[commitments](OpeningCommitmentVectorCost.lean), fully materialized
[node and group scalars](OpeningScalarVectorsCost.lean), the original
[point sets](OpeningPointSetsCost.lean), interpolation, and the final commitment
and scalar fold. Its erasure is the existing public reconstruction with its
symbolic MSM evaluated. The [total bound](PublicOpeningCostBound.lean) retains
all polynomial preparation, indexed reads, and list construction, together with
the full costs of the supplied quotient scalar and other input readers.
[Complete claim preparation](PlonkClaimConstraintsCost.lean) now constructs
the original queries, permutation records and column pairs, and lookup inputs,
then evaluates every constraint. Its [cost bound](PlonkClaimConstraintsCostBound.lean)
derives the required record and list bounds from their constructors and actual
key sizes. The [complete inferred quotient](PlonkVerifierHxCost.lean) adds domain
powering, all Lagrange values, output materialization, and the final fold and
division. Its [total bound](PlonkVerifierHxCostBound.lean) covers the same reference
calculation at every challenge value.
The model prices field and group primitives explicitly and counts structural
operations; it is not a machine-code correspondence theorem. Concrete
public-row and setup representations, encoding,
and the final Action composition remain to be counted. PRNG-class membership
additionally needs the cost of the
real prover and the supplied verifier-view test.

The [finite retry theorem](ActionFiatShamirRetry.lean) now compares complete
histories while the attempts share one evolving oracle cache. Each attempt uses
fresh private randomness; the public statement and witness stay fixed. The
adversary may query before selecting that request and after receiving the entire
history, with no intervening adversary queries during the internal retry run.
Only `retryRandomness` continues. Completion, the terminal opening error, and
simulator programming failure stop; exhaustion of the finite budget stays visible.
For `m >= 1` Actions and at most `n` attempts the two-sided error is bounded by

```text
error_retry(m, q_pre, n) = n * epsilon_bits(m, q_pre) + 11n(n-1) / p
                       <= n * m * 2^-238 + (n * q_pre + 11n(n-1)) / p.
```

[State-dependent composition](StatefulRetrySimulation.lean) charges the growing
cache without assuming independent retry decisions. [The tape law](OracleRetryTape.lean)
proves equality with the deterministic retained-history runner. Every stored
answer [survives the run](ActionOracleRetryResources.lean), and the final cache
has at most `q_pre + 22n + q_post` entries. The simulator's complete tape
allocation has `n * 512 * (132m + 58)` bits. This bound covers every finite
budget, including zero, and charges the entire available attempt capacity.

The [unlimited shared-oracle theorem](ActionOracleStreamSimulation.lean) instead
weights each continuation by the simulator's retry probability. For a fixed valid
request and any prior cache of at most `q` entries, define

```text
b(m) = F(m) + epsilon(m) + (132m + 36) delta
C(m,q) = 2 * epsilon_bits(m, q + 22)
       < 2 * (m * 2^-238 + (q + 22) / p),  for m >= 1.
```

The [retry-rate certificate](ActionOracleRetryGeometric.lean) proves `b(m) < 1/2`
for `1 <= m <= 65535`; that range is sufficient, not a protocol maximum. Whenever
`b(m) <= 1/2`, the two-sided error is at most `C(m,q)` for every finite budget and
for **every measurable event of the complete infinite observed stream**. The
[stream construction](ActionOracleStream.lean) retains every attempted result and
intermediate public cache, including programming failure and an infinite run if
one occurs. It pads stopped histories with absent entries. Private randomness is
fresh for each attempt, the request stays fixed, and there are no intervening
adversary queries. The limit proof does not treat cached responses as fresh
independent challenges or assume termination of the real prover.

The [termination and truncation bounds](ActionOracleStreamTermination.lean) show
that the simulator terminates almost surely. Real nontermination has probability
at most `C(m,q)`. Truncating after `n` attempts changes the simulated distribution
by at most `b(m)^n`, and the real distribution by at most `b(m)^n + C(m,q)`.
This complete-stream theorem is stated for a fixed request and arbitrary retained
cache; the adaptive before/after experiment above has its own finite-budget
theorem. These probability bounds do not establish machine running time. The
seeded-generator extension below adds its explicit PRNG assumptions.

The [continuing-generator runner](ActionGeneratorRetry.lean) now carries one
private generator state through those retries. Every started attempt allocates
its full `148m + 46`-word block, discarding any words that its early-abort path
does not use. A terminal result stops before allocating another block. The private
state advances through exactly the started attempts, and the complete observed
history equals replay from the generator's budget-length prefix. Oracle reply
slots remain separate from the private generator, and its final state is private.

The [finite PRNG reduction](ActionGeneratorPrng.lean) initializes that generator
once from a fresh uniform bit seed after adaptive preprocessing. For every
admitted retry-and-postprocessing test, the simulation error is at most
`error_retry(m, q_pre, n) + eta`. Here `eta` is the distinguishing bound for the
whole generated prefix, with [exact capacity](ActionPrivateRetryBits.lean)
`512 * n * (148m + 46)` bits. The proof assumes no independence of generated
blocks. It proves equality of the actual execution and security-game observation,
including retained failures, exhaustion, and the final oracle cache. Concrete
generator security, reduction-class membership, and a running-time proof remain
explicit obligations. This allocation policy makes no Rust cursor-parity claim.

The [complete seeded stream](ActionGeneratorStream.lean) now initializes that
generator once and runs with an independent infinite public reply tape. Every
finite projection equals the actual continuing-generator execution, including
intermediate public caches; private generator states stay hidden. For a fixed
valid request, prior cache of length `q`, and cutoff `n`, the
[unlimited PRNG reduction](ActionGeneratorStreamPrng.lean) bounds both directions
of every admitted tested comparison by

```text
error_seeded_infinite(m,q,n) = 2 * (C(m,q) + b(m)^n + eta).
```

Here `eta` bounds distinguishing the whole generated private prefix from uniform,
with the same capacity `512 * n * (148m + 46)` bits. Two explicit finite reductions
must be admitted: the test of the clipped verifier view and the actual exhaustion
bit. The [exhaustion reduction](ActionOracleRecordedPrng.lean) gives a generated
tail at most `b(m)^n + C(m,q) + eta`, which pays for truncating the actual unlimited
execution. The comparison charges `eta` twice, once per reduction. For
`1 <= m <= 65535`, `b(m)^n <= (1/2)^n`; the general theorem takes `b(m) <= 1/2`.
[Nontermination has the same tail bound](ActionGeneratorStreamTermination.lean)
and remains part of the observed experiment. Neither independent PRNG blocks nor
almost-sure seeded termination is assumed. The theorem fixes the request and
initial cache; concrete PRNG security, resource-class membership, and runtime
remain explicit premises or separate work.

The current [Action compiler reference theorem](ActionCompilerSimulation.lean) gives a
numerical statistical honest-verifier simulation bound for a complete encoded reference
attempt. It assumes original gate, lookup, and copy-value validity, eleven IPA rounds,
and a nonidentity blinding point. The concrete circuit and selector properties are proved.
It uses the actual Action
compiler key, Action's canonical public inputs, and
compiler-derived fixed rows, sigma rows, and complete ordered copy list. Sigma coherence
and every public polynomial degree bound are derived. The existing Action compiler
proofs discharge its fixed-column prefix, permutation count, and operation-footprint
bounds. [Action configuration](ActionConfiguration.lean) also supplies the complete
advice and instance query order, the permutation columns, and all degree-derived
dimensions. The [compression certificate](ActionCompressionCertificate.lean) proves
that the actual compiler produces fifteen compressed selector columns. The
[derived key](ActionDerivedKey.lean) has the required shape, fixed-query order,
domain, sigma naming, copy-query layout, and product dimensions. The
[compiled masking profile](ActionBoundaryProfile.lean) is derived from the actual
source and boundary values: structural certificates for every source gate and lookup
survive selector substitution, query resolution, and verifier-expression translation.
The [complete degree profile](ActionGateDegree.lean)
now follows from the actual source expressions and compiler: gates have degree
at most nine, lookup inputs at most four, lookup tables at most one, and permutation
chunks have width at most seven. The selector packer's degree invariant holds for
every activation pattern; this proof does not assume its final packing trace.
There is no unbounded row-failure term under those premises.
The [complete source selector trace](ActionSourceSelectorTrace.lean) now connects
all 395 Action regions to the compiler's activation walk. The proof composes
witness loading, both Merkle paths, the commitment and integrity checks, both
note commitments, and the final cross-address check. It retains empty regions,
duplicate activations, selector indices, and local rows, while proving independence
from the witness programs. The variable-base main region enables only selector
eight at local row zero. The [initial inactivity certificate](ActionInitialSelectorTrace.lean)
now excludes all nine previous-row selectors from global row zero, for any
nonnegative placement. The [ordered-summary refinement](ActionTracePlacement.lean)
also reproduces the actual V1 region starts, including the order of tied regions,
from reduced source data. The [replacement-value theorem](ActionSelectorReplacement.lean)
proves that each inactive guard still vanishes after compression, including when
another selector in its column is active. It uses the compiler's actual fixed-cell
writes and the packer's distinct root assignments. The
[boundary-value refinement](ActionBoundaryValues.lean) now incorporates these values
into the complete masking profile and main simulation theorem. It removes the
initial packed-column zeros and selector-routing premises. The checked compression
count removes the final concrete selector premise from the main theorem.
The [ordered shape certificate](ActionOrderedShapes.lean) reduces all 395 regions
to 57 distinct source shapes, with separate kernel-checked equalities for the four
Action stages. It retains selector columns, their order, and both empty regions.
[Planner start reconstruction](PlannerStarts.lean) proves how a lawful compact
placement trace supplies every individual V1 start. The
[concrete placement certificate](ActionOrderedPlacement.lean) checks all 181
nonempty-region blocks and returns all 395 starts, including both empty regions.
The [exact legacy-sort certificate](ActionOrderedSort.lean) checks all 23 recursive
phases, including tied keys, against those source shapes. The
[source-order reconstruction](ActionOrderedStarts.lean) connects that order to the
placement blocks and restores all 395 compiler starts to their original region indices.
The [compression-input refinement](ActionCompressionInput.lean) proves that the
actual compiler's column count is exactly `actionOrderedSelectorCount`, a finite
calculation using these certified source shapes, activations, and selector degrees.
The [closed numerical certificate](ActionCompressionCertificate.lean) checks all
6,795 source activations at those starts and proves that the count is fifteen.
The [bit-vector refinement](SelectorActivationBits.lean) preserves the complete
activation table and its conflict tests, including duplicate and out-of-range
activations. The [packing refinement](SelectorBitPacking.lean) gives exactly the
same greedy column count through this compact representation.
The finite equalities use [kernel reflexivity](../../Meta/KernelRfl.lean), which
checks each auxiliary theorem before closing its goal. Regression checks reject
false results and changed recursive-callback arguments. No new native certificate
is introduced.
The [encoded-attempt theorem](PlonkAttemptSimulation.lean) preserves this bound while
retaining partial output, the received challenges, and the specified failure status.
The [full-attempt failure bound](PlonkFailures.lean) is now numerical too. These results
compare unconditioned attempts. The [successful-view capstone](PlonkCompilerSuccess.lean)
now proves positive normalizers and carries their cost into the conditional comparison.
The [retained-retry capstone](PlonkCompilerRetry.lean) compares the complete observed
history for every finite independent attempt budget. The
[unlimited Action theorem](ActionRetryLimit.lean) now constructs a normalized stopped-history
law, proves its exact finite projections, and preserves the same uniform error bound.
The [Vesta specialization](VestaSimulation.lean) now fixes the encodings and derives the
blinding bijection from nonidentity; all four captured blinding points have kernel-checked
nonidentity proofs. Its curve-order dependency is recorded in a separate census.
The [verifier-grouping refinement](PlonkVerifierGrouping.lean) derives the exact five group
ID lists and node order from the actual query assembler for every positive Action count.
It proves that the verifier's compressed commitments agree with the reference construction
under the key layout, distinct rotation points, and public commitment agreement conditions.
Both captured keys have [kernel-checked query-layout certificates](PlonkQueryCertificate.lean).
The [scalar-routing refinement](PlonkEvaluationCompression.lean) also derives the duplicate
guard, every member evaluation, and each complete compressed evaluation vector. The
[final opening connection](PlonkVerifierOpening.lean) proves that the actual verifier's
assembled commitment point and scalar equal the reference reconstruction under the stated
key and point conditions. The [compiler-derived key connector](PlonkDerivedKey.lean)
supplies public commitment agreement from actual key generation. The concrete Action
opening connection obtains its shape and query layout from configuration and the
proved compression count. The witness and public-parameter assumptions, retry scope,
and separate implementation claims are described below.

The target for the specified interactive protocol is **statistical HVZK**. The
[Halo2 book's perfect SHVZK model](https://zcash.github.io/halo2/design/protocol.html)
restricts the verifier's challenge space, including excluding zero and evaluation-domain
points. The pinned implementation does not enforce all those exclusions. Exact conditional
simulation of a component is therefore not a perfect SHVZK theorem for this prover. Neither
the nonuniform sampler nor an upper bound on simulation error alone disproves perfect ZK.
The domain-row disclosure result below separates complete reference-proof distributions.
Under explicit compiler size and row bounds, a second valid reference witness can now be
constructed from any first one, using the compiler's complete ordered copy list. Turning
that result into an implementation counterexample still requires Rust witness admissibility
and execution correspondence.

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
not condition on success.

`m` is the number of Actions. `148m + 46` counts the prover's private random field
elements for one proof attempt—used to mask witness data and blind commitments.
That is 1,552 / 2,736 64-bit words for one / two Actions.
[PlonkSampling.lean](PlonkSampling.lean) connects this count to the complete
deterministic reference-prover tape described below.

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
These component bounds alone do not establish a joint transcript law. The joint algebraic
simulation below composes them with the pre-IPA messages under explicit quotient and
challenge premises; a full execution including failures remains a separate obligation.

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

The result retains correlations within this projection. The pre-IPA development below
connects the additive offset to the pinned opening groups and includes the other scalar
messages. The multi-opening construction below supplies valid IPA input from actual group
evaluations; its connection to the full emitted transcript remains open. These theorems
have supplied distinct evaluation points; they do not condition on a Fiat–Shamir
execution's observed challenges.

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

These IPA results start from a valid public opening. The joint algebraic construction below
derives that opening under explicit quotient-correctness premises and supplied challenges.
Handling failures across the full specified computation remains open. Fiat–Shamir
zero-knowledge, concrete PRNG security, and correspondence with a Rust executable are
separate claims. The interactive protocol theorem uses the independent random-bit tape
law stated in the description; it does not require verifying a concrete PRNG.

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

[PlonkDisclosure.lean](PlonkDisclosure.lean) now connects the observation to the complete
reference `ProofString` and challenge tape used by the numerical simulation theorem.
`plonkVerifierProofFromTape` composes the existing full-tape computation and proof
projection; sampling it gives exactly `sampledPlonkVerifierProver`. Every private tape
emits the original usable cell in the corresponding current-row advice slot when
`x = omega^row`, independently of the quotient, commitments, and IPA tail.

The exact joint event `(x = omega^row, adviceEval = value)` has mass `Pr[x = omega^row]`
when `value` is that cell and zero otherwise. Consequently, two supplied row vectors
with different cells have different complete reference-proof laws. Under the wide
challenge law, their event bias is at least `fieldSample (omega^row) > 0`, and no single
exact simulator law can match both. The pointwise disclosure does not rely on a
uniform-mask assumption or on the sampling-bias upper bound.

[PlonkInactiveRows.lean](PlonkInactiveRows.lean) and the kernel checks in
[PlonkInactiveCertificate.lean](PlonkInactiveCertificate.lean) prove that the captured
one- and two-Action gate and lookup expressions ignore all advice when packed selectors
are zero. Compiler support supplies these zeros after region placement, independently
of table values in the original fixed columns.

[PlonkUnusedWitness.lean](PlonkUnusedWitness.lean) changes one advice cell in usable row
2000. If placement ends by row 1999, earlier expressions cannot read the changed cell
through any supported rotation, and later expressions ignore it. Gate and lookup validity
therefore survive every replacement. Copy validity also survives if the declared copy
list avoids row 2000; that public footprint condition remains explicit.

[PlonkUnusedSimulation.lean](PlonkUnusedSimulation.lean) adds one to the cell, constructing
a distinct witness valid for the same reference key and public polynomials. Its
`keygenPlonkReference_no_perfect_simulator` theorem rules out an exact simulator for all
valid inputs to this reference relation under those placement and copy conditions.
[PlonkUnusedCertificate.lean](PlonkUnusedCertificate.lean) specializes the valid-witness
construction to both captured keys, discharging their inactive-expression checks.

[KeygenCopyRows.lean](KeygenCopyRows.lean) now takes the copy stream directly from the
compiler's V1 extraction and deferred constant allocation. Existing structural extraction
theorems prove its row and column bounds. [PlonkKeygenCopies.lean](PlonkKeygenCopies.lean)
packs every copy into the reference prover's cell type. Re-encoding recovers the complete
ordered source list, so the adapter drops no copies. Both captured keys have kernel-checked
seven/seven/one widths in [PlonkCopyCertificate.lean](PlonkCopyCertificate.lean).

[PlonkUnusedKeygen.lean](PlonkUnusedKeygen.lean) uses that computed list in the valid-witness
construction and the no-perfect-simulator theorem. A compiler operation footprint ending
by row 1999 supplies both selector placement and the unused-row copy condition. The theorem
therefore needs no separately supplied copy list or assertion that it avoids row 2000.
This endpoint retains public size and footprint bounds, original witness validity, and
sigma coherence. [PlonkCompilerSimulation.lean](PlonkCompilerSimulation.lean) derives that
coherence using the actual compiler sigma table and retains only original copy-value
equations as the copy-validity premise. Matching the compiler's column meanings to the
verifier key also remains open.

An Ironwood implementation counterexample still requires establishing whether Rust admits
the changed unused cell and matching its execution, aborts, retries, and encoding. The
witness construction does not assume that arbitrary changes to padding survive the Rust
witness-generation interface.

## Joint columns and pre-IPA messages

[ColumnSequence.lean](ColumnSequence.lean) extends the column result to a sequence of
retained-row constructors that may read **all earlier private masked rows**. The induction
removes the future view for each private history, so it does not assume independence merely
from earlier disclosed evaluations. [PlonkColumns.lean](PlonkColumns.lean) installs the
ten advice, six lookup-permutation, and six product columns per Action, including their
six-row and five-row suffix sizes.

[ColumnAttempt.lean](ColumnAttempt.lean) adds partial constructors that stop at the first
failure. The result retains the private prefix and a completion flag. Every produced
column uses exactly its earlier masked history and preserves the constructor's retained
rows. The prefix agrees with the corresponding prefix of the total comparison run;
completed attempts agree with that entire run on the same tape. These are execution
equalities, not distributional claims conditioned on successful construction.

[PreIpaMask.lean](PreIpaMask.lean) jointly simulates all pre-IPA commitments, five common
evaluations of every private column, `r(x)`, and the masked `Q₀(q)`. The unblinded commitment
cores may depend on all private rows and both coefficients of `r`. Independent commitment
blinds hide them jointly with the scalars. Under ideal field samples, the view has an exact
public simulator law when the observation points are distinct, off the row domain, and
`q ≠ x`.

[ColumnTape.lean](ColumnTape.lean) first proves a canonical interleaved representation.
[BatchedTape.lean](BatchedTape.lean) and [PlonkTape.lean](PlonkTape.lean) then convert the
actual batch layout observed in the available Bento checkout
`e32e61eb35b6e5b5e0600cb0903adcfe0cd617d8`, at
`crates/sensei/src/native/randomness.rs`: ten advice tails before their ten blinds per
Action; both lookup tails before their two blinds; singleton product batches. Each
equivalence preserves the tail and blind subsequences. This establishes the model's
`148m` private-column draws and `148m + 12` pre-IPA draws; adding the IPA's 34 gives
`148m + 46`. The available checkout has not been identified with the description's
`56a7de7` revision. These equivalences concern the Lean sampling programs; they do not
establish the separate claim of Rust execution correspondence.

[PlonkOpening.lean](PlonkOpening.lean) constructs the pinned five opening-polynomial groups
and their Horner folds. It proves that `Q₀(q)` is precisely the first group's weighted
prefix plus `r(q)` at coefficient one, even for zero `x₁`. Each remaining group value is a
fold of the column evaluations at `q`. The collapsed quotient `H_x` may depend on every
private row; its value at `q` remains hidden inside `Q₀(q)`.

[PlonkTranscript.lean](PlonkTranscript.lean) computes the emitted step-5 scalar sequence and
the five step-6 group evaluations from those polynomials, and proves that together with the
commitments they are a public projection of the joint mask view. The simulator receives
only public polynomials and challenges. For the batched wide-reduction sampler, the entire
algebraic pre-IPA message view has two-sided event error at most
**`(148m + 12) × bias`**, with supplied distinct points
`x, xω, xω⁻¹, xω⁻⁶, q` outside the 2048-row domain.

That hiding result quantifies over supplied retained-row algorithms, quotient pieces, and
unblinded commitment cores. The joint construction below instantiates the cores and
composes with the IPA. The row and quotient algorithms, their constraint correspondence,
early failures, and the actual challenge law still require integration. These results do
not condition a Fiat–Shamir execution on its challenges or establish whole-prover HVZK.

## Computed multi-opening and IPA input

[MultiopenPolynomial.lean](MultiopenPolynomial.lean) computes each group's interpolant,
vanishing polynomial, and quotient `(Q_i − R_i) / V_i`. For actual evaluations at distinct
nodes, it proves exact divisibility and that the folded `Q'` evaluates to the scalar
reconstructed by the existing `multiopenEval` verifier routine when `q` avoids those nodes.

[PolynomialCommitment.lean](PolynomialCommitment.lean) connects the coefficient-vector
commitment to both polynomial and blind folds. [MultiopenIpa.lean](MultiopenIpa.lean) uses
those identities to derive both valid-opening premises of the IPA theorem: the existing
`multiopenCombine` commitment opens to the computed `P` with the actually folded `ρ_P`,
and its reconstructed value equals `P(q)`. Degree bounds prove that converting `P` to an
IPA vector does not truncate any coefficients.

[PlonkMultiopen.lean](PlonkMultiopen.lean) instantiates this with the exact five pinned
groups and their point sets. It includes blind one for public instance, fixed, and `σ`
polynomials, the weighted sum of the eight quotient-piece blinds in `H_x`, and each
private column's blind. Private-row polynomials and the linear mask satisfy the degree
bound by construction; bounds on the supplied public polynomials and quotient pieces
remain explicit premises.

The resulting IPA transcript has an exact ideal simulation and a two-sided
**`34 × bias`** bound with wide-reduced IPA coins, for nonzero `ξ` and round challenges.
These results hold for every preceding private state and do not assume that the incoming
blind is independent of earlier messages. They still start from the resulting public IPA
opening. The next construction rebuilds it from the public mask view, assuming agreement
of the inferred `H_x(x)` with the honest quotient. The verifier-typed construction below
instantiates the constraint function; the later opening connector derives the actual
proof's query routing and final assembly under explicit key and point conditions. The available
Rust implementation's repeated synthetic division has not yet been related formally to
this quotient computation.

## Joint algebraic prover simulation

[PlonkCommitments.lean](PlonkCommitments.lean) instantiates every pre-IPA commitment core
with its actual coefficient polynomial: the private row columns, linear mask, eight
quotient pieces, and computed `Q'`. It reads their blinds from the same commitment positions.
The polynomial-only `Q'` construction is independent of every commitment blind.

[PlonkPublicOpening.lean](PlonkPublicOpening.lean) reconstructs the five group commitments
and all their node evaluations from the enriched public view. It proves that applying the
existing `multiopenEval` and `multiopenCombine` operations gives the honest IPA input.
The inferred `H_x(x)` comes from a supplied public function `expectedHx`. Agreement of that
function with the honest quotient is an explicit premise. The construction below
instantiates it with the verifier's actual constraint calculation.

`idealPlonkJoint_simulation_capstone` in [PlonkComposition.lean](PlonkComposition.lean)
proves exact equality of the **joint pre-IPA view and complete IPA transcript** with one
public simulator under ideal field samples. The proof first simulates the IPA for each
reachable private state, then replaces the preceding public-view distribution. It retains
the actual dependence of the IPA polynomial and blind on all earlier private coins.
Degree bounds and quotient agreement are required only for row states in the honest
construction's support. They are not yet derived from an Orchard witness relation.

[PlonkSampling.lean](PlonkSampling.lean) connects this joint computation to the batched
pre-IPA tape and ordered IPA suffix. All `148m + 46` field draws feed one deterministic
prover computation. `sampledPlonkJoint_simulation_error_bound` gives the two-sided event
bound **`(148m + 46) × bias`** against the same simulator. Its premises remain: a blinding
generator spanning the group; the quotient and degree obligations above; nonzero `ξ` and
IPA round challenges; and five distinct observation points outside the 2048-row domain.
The challenges are supplied inputs, not a conditioned Fiat–Shamir transcript.

[PlonkSimulator.lean](PlonkSimulator.lean) implements the joint simulator from field coins.
It samples points as multiples of `W`, samples the column observations directly, rebuilds
the public IPA input, and runs the existing IPA simulator. Its field-coin law is proved
equal to the simulator used by the joint theorem. No witness, private row or quotient
constructor, or discrete-log inverse appears in this algorithm.

## Computed quotient and verifier-typed proof

[PlonkProofString.lean](PlonkProofString.lean) projects the joint view into the existing
`ProofString` at the captured Orchard dimensions. Its `plonkVerifierHx` calls the existing
`allExpressions` and `expectedHEval` functions. It proves that this public calculation
is exactly the quotient value inferred from the projected proof. The calculation reads
only the public key, statement polynomials, challenges, and column claims.

[PlonkConstraints.lean](PlonkConstraints.lean) constructs the gate, permutation, and lookup
numerator from the actual rotated row polynomials and canonical Lagrange selectors.
`plonkConstraintNumerator_eval` proves that its evaluation is the verifier's precise
constraint fold. [QuotientPieces.lean](QuotientPieces.lean) computes polynomial division by
`X^2048 - 1` and cuts eight consecutive coefficient blocks. Recombination, per-piece degree
bounds, and quotient agreement are proved from divisibility and numerator capacity.

`sampledPlonkVerifier_simulation_error_bound` in
[PlonkQuotientSimulation.lean](PlonkQuotientSimulation.lean) uses these computations to
simulate the **complete algebraic `ProofString`**, with the same two-sided
**`(148m + 46) × bias`** bound. An arbitrary quotient constructor and arbitrary inferred-value
callback are no longer inputs. Instead, each reachable honest row state must produce a
numerator divisible by `X^2048 - 1` and of degree below `9 × 2048`; public polynomial degree
bounds and the earlier challenge/generator conditions remain explicit. The next result
derives the capacity requirement from public circuit syntax.

[LookupDegree.lean](LookupDegree.lean) keeps the lookup input and table degree bounds
separate. [PlonkDegree.lean](PlonkDegree.lean) then proves the full numerator has degree at
most `9 × 2047`, for every row state, from a public profile: gate degree at most nine,
permutation chunks of at most seven columns, lookup input degree at most four, and table
degree at most one. [PlonkDegreeCertificate.lean](PlonkDegreeCertificate.lean) kernel-checks
that profile for both captured keys without using their earlier native certificates.

`sampledPlonkVerifier_capacity_simulation_error_bound` in
[PlonkCapacitySimulation.lean](PlonkCapacitySimulation.lean) supplies that derived capacity
to the complete algebraic proof simulation. Divisibility of the constraint numerator on
each reachable row state remains the only private-state premise. The public polynomial,
generator, and supplied-challenge conditions still apply.

[DomainDivisibility.lean](DomainDivisibility.lean) proves that vanishing on every domain
row is equivalent to divisibility by `X^n - 1`. It applies this to the actual constraint
fold. `sampledPlonkVerifier_rows_simulation_error_bound` in
[PlonkRowSimulation.lean](PlonkRowSimulation.lean) therefore derives both quotient
premises from public degree bounds and row-wise satisfaction of the gate, permutation,
and lookup constraints. The concrete construction theorems below now supply the lookup
and product-scan parts, deriving the copy-product identity from original copy equations
and public sigma coherence. The original-row theorems below also supply gate preservation
and construction completion from original validity and public mask checks. The circuit's
public-polynomial/keygen connection and whole-prover exceptional behavior remain open.
Satisfying advice columns are inputs
in the pinned protocol; generating the underlying circuit witness is outside its scope.

[ExceptionalMixtures.lean](ExceptionalMixtures.lean) and
[PlonkExceptional.lean](PlonkExceptional.lean) remove the requirement that every random
row state has a valid quotient. They retain the probability of exceptional private states
under the ideal row law and add it to the complete sampling bound. The comparison uses
the original, unconditioned row distribution and the inherited IPA blind.

`sampledPlonkVerifier_consistency_error_bound` in
[PlonkConsistency.lean](PlonkConsistency.lean) applies this to the computed numerator and
existing proof type. Its bound is **`invalidRowMass + (148m + 46) × bias`**. The first term
is the ideal probability that `X^2048 - 1` does not divide the actual numerator. The
theorem no longer assumes row correctness; a separate result bounds that term by the
probability of any violated row constraint. The construction results below bound it
using fresh product challenges and explicit original-witness and public-key conditions.
Public polynomial, degree-profile, generator, and supplied-challenge premises still apply.

[PlonkChallenges.lean](PlonkChallenges.lean) records all `11 + k` verifier challenges in
their squeeze order and defines both uniform and wide-reduced independent tape laws.
Replacing this tape's field samples costs at most `(11 + k) × bias`.
`freshPlonkVerifier_simulation_error_bound` in [PlonkFresh.lean](PlonkFresh.lean) retains
the complete challenge tape alongside the existing `ProofString`. Its bound is:

**`badChallengeMass + averageInvalidRowMass + (148m + 46) × bias`**.

This result no longer assumes a good fixed challenge tape or correctness on every private
row state. It samples the original challenge law without rejecting exceptional values,
and averages row inconsistency over that law. The simulator uses only the public input
and the same challenge law. Independent verifier coins do not establish Fiat–Shamir
zero-knowledge.

[PlonkChallengePoints.lean](PlonkChallengePoints.lean) and
[PlonkChallengeBounds.lean](PlonkChallengeBounds.lean) bound the public exceptional event
by **`(k + 4102)/p`** for uniform coins, plus **`(k + 11) × bias`** for wide reduction.
This counts `x = 0`, `xi = 0`, the `k` zero folding challenges, two size-2048 domain-hit
events, and four collisions between the later point and a rotated first point.
At `k = 11`, `wideFreshPlonkVerifier_simulation_error_bound` in
[PlonkFreshBounds.lean](PlonkFreshBounds.lean) gives:

**`averageInvalidRowMass + 4113/p + (148m + 68) × bias`**.

The row term averages the ideal private row law over the wide-reduced verifier law.
The concrete construction bound below now separates its zero-denominator contribution
from the remaining sorting and gate prerequisites, given original copies and public
sigma coherence. The causality theorem below connects the reference tape experiment to
the actual interactive schedule.

## Complete encoded attempts

[ProverAttempt.lean](ProverAttempt.lean) interprets the existing typed transcript schedule
with supplied point and scalar codecs. A failed point encoding emits no bytes for that
point and requests new randomness. A post-challenge failure retains that challenge.
The kernel-checked prefix theorem proves that adding any messages after a failed prefix
does not change the observation. Completed attempts emit every point/scalar encoding;
challenge markers contribute no proof bytes.

[PlonkAttempt.lean](PlonkAttempt.lean) reuses the existing verifier's `preIpaTranscript`,
then appends its round blocks and final `c,f` scalars. It receives exactly `11+k` challenges
in the existing order. After `x1,x2` it reports the duplicate-opening error if `x = 0`;
the proof identifies that check with distinctness of the actual interpolation node lists.
Each zero IPA round challenge requests fresh randomness after both round points.
For a codec that fails precisely on the identity, completion is equivalent to all emitted
points being nonidentity, `x ≠ 0`, and all round challenges being nonzero. No other
challenge exclusions are enforced by this observer.

`wideObservedCompilerKeygenPlonk_simulation_error_bound` in
[PlonkAttemptSimulation.lean](PlonkAttemptSimulation.lean) compares the entire encoded
observation: emitted bytes, received challenges, attempt status, and the verifier's full
tape, including unused coins. Its two-sided bound is unchanged:
**`(42882m + 4113)/p + (148m + 70) × bias`**. The simulator still has no witness argument.
This is post-processing of the compiler-derived reference law under the same witness
and public-key premises. It does not condition away failures.

The common public initialization is fixed separately and contributes no proof bytes.
The unconditioned bound holds for every supplied deterministic codec, so encoding adds
no simulation error. The successful-output analysis below uses the specified codec's
identity-failure property. The retained-history analysis below uses the observer's exact
retry/error distinction. The causality proof below connects this observation to the
complete reference computation on a fixed private tape.

### Specified encodings and Vesta blinding

[ProofEncoding.lean](ProofEncoding.lean) supplies the specified codecs: a scalar's
canonical 32-byte little-endian representative, and a nonidentity Vesta point's
32-byte affine x-coordinate with y-parity in bit 255. The point writer fails exactly
on the identity. The point codec reuses CompElliptic's existing compressed encoding;
neither codec adds a hash or proof trailer.

[ProofSize.lean](ProofSize.lean) counts the actual reference proof constructor and
existing message schedule, including the two optional permutation evaluations per
Action. At eleven IPA rounds there are exactly `85+71m` proof items. With the fixed
codecs, [PlonkEncoding.lean](PlonkEncoding.lean) proves that every completed reference
attempt has exactly `2720+2272m` bytes. The same observer preserves the full reference
prover's causal prefixes and the specified failures.

`freshEncodedPlonkReferenceAttempt` samples the independent wide-reduced private and
verifier tapes and runs the fixed-tape reference observer. Its law theorem identifies
this computation exactly with the existing fresh reference proof law followed by the
canonical observer. The simulator comparison therefore concerns those actual encoded
attempts, including partial output and failure status.

[BlindingGenerator.lean](BlindingGenerator.lean) proves that scalar blinding by a
nonzero point is injective in a field module and bijective when the group and scalar
field have the same finite cardinality. [VestaBlinding.lean](VestaBlinding.lean) derives
that cardinality condition for Vesta, so the simulation's hiding premise is equivalent
to `W != 0`. [CapturedBlinding.lean](CapturedBlinding.lean) proves this nonidentity for
all four checked-in URS captures. The coordinate lookups and curve equation use kernel
reduction; the captures' native whole-point-list certificates are not used.

[VestaSimulation.lean](VestaSimulation.lean) applies these facts to the compiler-derived
attempt, successful-emission, and finite retained-retry theorems, with the same numerical
bounds. The codecs are fixed and the blinding premise is reduced to nonidentity. The
actual Action mask and key conditions remain explicit; the later opening connector
derives verifier grouping from the query layout. The Vesta
group-cardinality and concrete scalar-module facts inherit the repository's existing
`CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt` native certificate. That dependency is named
in [Vesta/TrustBoundary.lean](Vesta/TrustBoundary.lean); no new native certificate is added.

## Challenge causality

[ProtocolCausality.lean](ProtocolCausality.lean) makes the interactive-execution
condition precise: after `n` received challenges, changing later challenges must leave
every message before the next receive unchanged. Its prefix operation preserves message
order and has exactly the claimed receive budget. The interpreter depends only on the
challenges and checks scheduled inside that prefix, including failed encodings.

[PlonkChallengeCausality.lean](PlonkChallengeCausality.lean) proves that the actual failure
checks satisfy this condition: the duplicate-opening check reads the already received
`x`, and each IPA retry check reads its current round challenge. A message producer
satisfying the prefix condition therefore has the same property after encoding and
these checks. The generic adapter keeps the message-producer condition explicit.

[ProtocolStages.lean](ProtocolStages.lean) and
[PlonkStageCausality.lean](PlonkStageCausality.lean) decompose the full existing attempt
trace into message blocks separated by receives. The equality preserves its exact order,
including empty blocks for consecutive challenges. A dependency proof for each message
block gives causality of the complete trace and its encoded observation. Once all
scheduled challenges agree, the whole typed challenge record agrees, so the final
scalars need no additional causality premise.

[PlonkRowCausality.lean](PlonkRowCausality.lean) proves further concrete dependencies on
every fixed replacement-row tape. Initial advice columns ignore the entire verifier
tape; the complete column state uses only `theta,beta,gamma`; quotient pieces additionally
use `y`. The existing [lookup-prefix result](PlonkPrefix.lean) places the intermediate
advice and lookup-permutation columns before `beta,gamma`. These statements include
the reference constructor's totalized fallbacks and require no witness-validity premise.

[TapeCausality.lean](TapeCausality.lean) and
[PlonkTapeCausality.lean](PlonkTapeCausality.lean) connect those facts to the complete
actual prover tape. The decoder depends only on mask boundaries and batch order;
changing retained-row callbacks changes none of the selected row masks, linear
coefficients, commitment blinds, or IPA suffix. The row-prefix facts therefore apply
to the actual decoded private material without a separate row-tape assumption.

[PlonkCommitmentCausality.lean](PlonkCommitmentCausality.lean) then proves the dependencies
of the emitted fields in the existing `ProofString`: advice precedes every challenge,
lookup permutation commitments use only `theta`, product commitments additionally use
`beta,gamma`, the linear-mask commitment ignores all challenges, and quotient commitments
add only `y`. The complete existing message prefix before the receive of `x` is proved
equal whenever those four already received challenges and the complete private tape
agree. These deterministic results require no sampling law or challenge exclusions.

[IpaCausality.lean](IpaCausality.lean) proves pointwise dependency facts for the actual
tape-based IPA computation. The sparse-mask commitment needs neither `xi`, `z`, nor any
round challenge. The pair in round `j` depends only on challenges from rounds strictly
before `j`; in particular it does not use the challenge received after that pair. These
proofs include zero challenges and invalid openings, and assume no sampling law.

[PlonkOpeningCausality.lean](PlonkOpeningCausality.lean) proves the remaining pre-IPA
dependencies on the complete private tape. The evaluation block uses the first four
column observations and `r(x)`, ignoring the later observation point. The `Q'` commitment
ignores `x3`, and the five group evaluations ignore `x4` and later challenges.
[PlonkIpaCausality.lean](PlonkIpaCausality.lean) connects the IPA dependency proofs to
the actual opening, coefficients, inherited blind, and suffix of that same private tape.
The mask commitment uses only `x3` and its own private coins; each round pair uses only
the preceding challenges. No valid-opening premise is needed for these dependencies.

[PlonkCausality.lean](PlonkCausality.lean) assembles these results for every stage of the
existing attempt trace. Its eleven-round `plonkReferenceProofFromTape` uses a fixed
`148m+46`-sample private tape, and `plonkReferenceProofFromTape_law` proves that sampling
this adapter gives exactly the existing wide-reduced reference-prover distribution.
`plonkReferenceProofFromTape_causal` proves causality of its entire message schedule;
`plonkReferenceProofFromTape_observation_causal` includes the encoded prefixes and actual
abort checks. Both statements hold on every private tape and for all challenge values,
without a randomness, witness-validity, or challenge-exclusion assumption. The canonical
codecs above now instantiate that observation. The concrete circuit/key and verifier
correspondence retain their separate obligations.

## Full-attempt failure probability

[PlonkPoints.lean](PlonkPoints.lean) proves joint uniformity of the pre-IPA commitments
under ideal field blinds, without requiring good challenges or valid row states. It
applies the IPA point bound conditionally on the entire preceding private state; the
inherited IPA blind is not assumed independent of that state. A union bound covers all
`22m+2k+11` emitted points. [PlonkAttemptPoints.lean](PlonkAttemptPoints.lean) connects every
point slot in the existing proof schedule to those families and transfers the bound
through the complete wide-reduced private tape.

[PlonkFailureChallenges.lean](PlonkFailureChallenges.lean) counts only challenges which
stop the attempt: `x = 0` and the `k` zero IPA round challenges. Their probability is at
most `(k+1)/p + (k+11) × bias` under the independent wide-reduced verifier law.

`widePlonkAttempt_failure_le` in [PlonkFailures.lean](PlonkFailures.lean) combines these
results. At eleven rounds, the probability of a retry request or the specified terminal
error is at most **`(22m+45)/p + (148m+68) × bias`**. For one Action this is
**`67/p + 216 × bias`**. The codec must fail precisely on the identity, and the usual
blinding-generator bijection is required. Completion means finishing the emission
schedule; the theorem does not assert verifier acceptance. The bound does not discard
exceptional challenges or assume row correctness.

## Successful full-prover views

[PlonkSuccessBounds.lean](PlonkSuccessBounds.lean) adds the honest failure bound `F(m)`
to the raw joint simulation error `epsilon(m)`. Their sum bounds failure on both sides:

**`B(m) = (42904m + 4158)/p + (296m + 138) × bias`**.

It kernel-proves `B(m) < 1` for `m ≤ 65535`, which includes both captured Action counts.
This is an arithmetic certificate; the general simulation endpoint retains `B(m) < 1`
as its numerical premise without imposing that range on the protocol.

[PlonkSuccess.lean](PlonkSuccess.lean) derives supported successful outcomes on both
sides before filtering either law. [PlonkCompilerSuccess.lean](PlonkCompilerSuccess.lean)
instantiates that argument with the existing compiler-derived prover and public simulator.
`wideSuccessfulCompilerKeygenPlonk_simulation_capstone` gives the two-sided bound
**`2 × epsilon(m) / (1 - B(m))`** for the full encoded view conditioned on completing the
emission schedule. The simulator is the existing public-data law conditioned on that
same observable event; its support certificate is an erased proof, not a witness input.
No actual success probability or conditional simulation statement is assumed.

Independent draws which discard unsuccessful observations converge to this conditional
law. The retry comparison now holds for arbitrary observation types, with no finite-type
instance required. Selecting completed attempts is distinct from the protocol's retry
policy: a terminal opening error is not a retry request. The next section models that
distinction while retaining earlier failed prefixes. Completion still means emitting the
full proof, without asserting verifier acceptance.

## Retained whole-prover retry histories

[RetryHistory.lean](RetryHistory.lean) gives a deterministic program on a finite attempt
tape. It retains every attempt up to the first outcome which does not request a retry,
and reports an exhausted budget separately. Appending unused future attempts after a
terminal outcome cannot change the history. The corresponding probability recursion is
proved equal to running this program on independent draws from the single-attempt law.

[PlonkRetry.lean](PlonkRetry.lean) uses the actual attempt observation to make its retry
decision. Only `retryRandomness` continues; both completed emission and the terminal
`coincidentOpeningQueries` error stop. Running the policy on encoded observations gives
the same result as observing the used raw attempts. Every failed prefix, received
challenge sequence, verifier tape, and status stays in the history. Each attempt uses
fresh independent private and verifier tapes, with the statement and witness unchanged.

[RetryHistorySimulation.lean](RetryHistorySimulation.lean) proves the joint comparison
for every finite budget `n`, with two-sided error at most
**`epsilon(m) × (1 + F(m) + ... + F(m)^(n-1))`**, and therefore at most
**`epsilon(m) / (1 - F(m))`** when `F(m) < 1`. A fresh attempt costs `epsilon(m)`;
the preceding real attempt's retry probability scales the continuation's error even
though that preceding observation is retained. The proof compares the joint history,
without replacing it by separate marginal comparisons.

`wideRetriedCompilerKeygenPlonk_simulation_capstone` in
[PlonkCompilerRetry.lean](PlonkCompilerRetry.lean) supplies the existing compiler-derived
prover and its public simulator to this bound. It keeps the same explicit circuit, key,
witness, and codec conditions. [PlonkFiniteView.lean](PlonkFiniteView.lean) supplies finite
raw attempt spaces for probability proofs; the sampler and simulator do not enumerate
them. Encoded histories still have arbitrary finite length.

The exhaustion probability is exactly the retry probability raised to `n`, hence at
most **`F(m)^n`** for the real law and **`B(m)^n`** for the simulator. Both tend to zero
when `B(m) < 1`, with the same checked certificate for `m ≤ 65535`.

[RetryTape.lean](RetryTape.lean) constructs a normalized law of complete stopped histories
by summing the independent probabilities of every finite retry prefix followed by a
terminal attempt. [RetryFlow.lean](RetryFlow.lean) proves that this law follows the
one-step retry policy, and [RetryProjection.lean](RetryProjection.lean) proves that
each finite truncation is exactly the established independent-tape execution.
[RetrySupport.lean](RetrySupport.lean) proves that every supported history is nonempty,
obeys the retry decisions, and ends in a terminal outcome. No failed prefix is discarded
or conditioned away.

[RetryLimit.lean](RetryLimit.lean) bounds the difference between a complete history and
its truncation by the geometric exhaustion tail. Taking both tails to zero extends the
two-sided **`epsilon(m) / (1 - F(m))`** bound to every event of the complete unlimited
history. The comparison now applies directly to arbitrary discrete encoded observations;
it needs no finite-type instance for the history space.
[RetryExpectation.lean](RetryExpectation.lean) proves that a retry probability `r < 1`
gives exact expected attempts **`1 / (1 - r)`**.

[ActionRetryLimit.lean](ActionRetryLimit.lean) instantiates these results with the closed
Action compiler theorem and canonical codecs. Its real and simulated expected attempts
are at most **`1 / (1 - F(m))`** and **`1 / (1 - B(m))`**, respectively. Its capstone supplies
the numerical condition for `m ≤ 65535`; this certified arithmetic range is not a protocol
maximum. The simulator uses only public data and an erased proof of positive stopping
probability. Both experiments stop almost surely under their specified independent-attempt
policy. A caller carrying prover or generator state across attempts, or retries sharing
a Fiat–Shamir oracle, needs a separate connection. Terminal emission still does not assert
verifier acceptance.

[RunningProductRows.lean](RunningProductRows.lean) gives computable lookup and chained
permutation ratio scans with `0` mapped to `0` on inversion. It proves the exact condition
for a row recurrence to fail: its denominator is zero and its required right side is
nonzero. Under the product identity, the terminal value satisfies `z²-z = 0` even when
denominators vanish. For lookups, permutations of the input and table prefixes supply
that identity. The sorter below supplies the lookup permutations; the copy theorems below
supply the permutation-column identity from original copies and public sigma coherence.
The zero-preserving fallback matches the available Bento source
at `e32e61eb35b6e5b5e0600cb0903adcfe0cd617d8`, in `crates/sensei/src/native/prover.rs`;
this does not identify that checkout with the Sensei revision named by the description.

[ProductDenominators.lean](ProductDenominators.lean) bounds zero factors fixed before
fresh `beta` and `gamma`, allowing a random private prefix independent of those draws.
The wide-reduced bound is **`(b + g)/p + 2 × bias`**, where `b` counts beta-only factors
and `g` counts gamma-linear factors. The dense declared dimensions—fifteen permutation
and six lookup factors per usable row per Action—give **`42882m/p + 2 × bias`**.
The concrete factor coverage and pre-product challenge dependencies are proved below,
and the final construction theorem applies this term to `averageInvalidRowMass` under
the complete independent challenge law. The original-row theorem below removes the
remaining circuit and sorting failure mass under explicit witness and public mask premises.

[LookupRowConstraints.lean](LookupRowConstraints.lean) proves that the computed lookup
scan satisfies all five constraints emitted by the existing `lookupExpressions` builder.
It uses the compression equations, permutations of the input and table prefixes, and
the sorted columns' first-row and run-structure facts, outside zero denominator factors.
The terminal and blinding rows keep their actual selector behavior; values switched off
by selectors are unrestricted.
[PlonkSelectorRows.lean](PlonkSelectorRows.lean) identifies those indicators with the
actual 2048-row selector polynomials, using the kernel-checked root certificate.
[LookupPolynomialRows.lean](LookupPolynomialRows.lean) supplies the rotated evaluations
and proves that every lookup constraint polynomial is divisible by the domain polynomial.
[PlonkLookupRows.lean](PlonkLookupRows.lean) identifies these records with the actual
proof string and each Action's entries in the honest constraint model.
This replaces a lookup-constraint correctness premise with explicit row-construction
facts. The sorter below supplies its permutation and run-structure facts. The later
construction theorems identify the prefix reads and computed scan with the final columns,
discharging those facts for completed reference attempts outside zero denominators.

[PermutationRowConstraints.lean](PermutationRowConstraints.lean) computes the
permutation factors using the verifier's exact column-name stride and chains the three
product scans. All seven existing permutation constraints follow from the scan, the full
product identity, and nonzero active-row denominators. The terminal rotation is used only
at row zero, and switched-off masked rows remain unrestricted. A separate lemma derives
the product identity on named cells from copy-preserving permutation wiring.
[PermutationPolynomialRows.lean](PermutationPolynomialRows.lean) transports these facts
through the actual polynomial builder to exact domain division.
[PlonkPermutationRows.lean](PlonkPermutationRows.lean) identifies the proof string's
next/terminal rotations, with a kernel proof that the inverse-sixth-power rotation reads
the retained row 2042 from row zero. The later construction theorems supply the scan
correspondence and exact packed constraint layout. The copy and original-row results below
instantiate the named-cell identity at those factors and prove gate preservation from
explicit witness and public-key conditions. The final reference theorem combines these
results with the numerical exceptional-event bounds.

[LookupSort.lean](LookupSort.lean) implements the sorting rule from step 2 of the pinned
description: canonical integer sorting, one matching table occurrence reserved at each
new input run, and ascending unused table values assigned to repeated-input positions
from highest row to lowest. Successful output preserves both multisets and satisfies
the first-row and run-structure rules.
[LookupSortSuccess.lean](LookupSortSuccess.lean) proves that equal-length valid lookup
prefixes always succeed; each input value only needs to occur somewhere in the table,
even if the input repeats it many times.
[LookupSortRows.lean](LookupSortRows.lean) specializes to canonical `Fp.val` order and
supplies these facts directly to the existing five lookup constraints. This closes the
sorter's correctness premises. The original-row theorem below supplies lookup membership
after masking under the public expression check. Rust control-flow correspondence remains
a separate obligation.
[LookupSortExamples.lean](LookupSortExamples.lean) kernel-checks small exact-order cases
for reverse filling, duplicate table occurrences, and an absent required value.

[PlonkRowConstruction.lean](PlonkRowConstruction.lean) supplies concrete advice,
lookup-sort, and product-scan constructors. Compression reads the existing polynomial
proof's query layout, including rotations of earlier masked advice. The permutation
factors resolve the key's actual packed references; a checked equality identifies
these pairs with the constraint model for a three-chunk key. Sorting failures remain
explicit. Checked lemmas show that lookup sorting uses only `theta`, and that
all row computations are independent of challenges after `theta`, `beta`, and `gamma`.

[PlonkConstruction.lean](PlonkConstruction.lean) installs those constructors in the
existing schedule and executes them from the empty history on `126m` row-mask samples.
Completed attempts agree exactly with a concrete total constructor accepted by the
joint simulation. Comparing wide-reduced and uniform field tapes costs `126m × bias`
for the entire attempt, including its failure flag and private prefix. Both laws still
use the same private witness; this comparison does not simulate construction failures.
The total comparison constructor replaces a failed sort by zero rows and therefore
cannot be identified unconditionally with the honest attempt.

[PlonkColumnOrder.lean](PlonkColumnOrder.lean) proves the four phase ranges in the actual
emission order. [PlonkColumnReads.lean](PlonkColumnReads.lean) uses those ranges to prove
that each construction reads exactly the same polynomials from its preceding private
prefix as from the final column state. This includes all rotated queries, both
computations of each lookup sort, and the inherited permutation seeds.

[PlonkConstructedRows.lean](PlonkConstructedRows.lean) then identifies the actual
polynomial rows produced by the attempt: usable advice equals the supplied witness,
both lookup columns come from one canonical sort, and every product follows the
computed scan through its retained terminal row. Its general retained-row theorem
also applies to columns already produced in a failed attempt's prefix.

[PlonkConstructedLookup.lean](PlonkConstructedLookup.lean) derives domain divisibility
of all fifteen lookup constraints per Action from completed construction and nonzero
denominator factors. It assumes no sorting or scan correspondence.
[PlonkConstructedPermutation.lean](PlonkConstructedPermutation.lean) identifies the
actual three-set/chunk layout and derives divisibility of all seven permutation
constraints from the executed scans, nonzero denominators, and the full packed
copy-product identity.
[PlonkConstructedConstraints.lean](PlonkConstructedConstraints.lean) combines these
results with gate correctness to derive division of every constraint and of the
actual numerator by `X^2048 - 1`.

[ColumnPrefix.lean](ColumnPrefix.lean) proves that equal construction prefixes and
matching tape entries produce equal column prefixes, even when the later steps and
total tape lengths differ. [PlonkPrefix.lean](PlonkPrefix.lean) applies this to the
computed first `16m` advice and lookup-permutation columns: on each fixed tape these
columns depend only on `theta`, independently of `beta`, `gamma`, and later challenges.
Their full polynomials and the packed permutation factors therefore agree. A uniform
fixed-size tape gives exactly the sequential row law used by the joint simulation.

[ProductDenominatorLists.lean](ProductDenominatorLists.lean) applies the finite-family
bound to computed lists, retaining duplicate factors.
[PlonkProductFactors.lean](PlonkProductFactors.lean) lists the actual lookup and packed
permutation factors and proves that avoiding their zeros gives all nonzero usable-row
denominators. The count is `(packedReferences + 6) × m × 2042`.

[PlonkProductBounds.lean](PlonkProductBounds.lean) combines this coverage with the
prefix theorem. Under two fresh independent wide-reduced product challenges, the
computed reference denominators have bad-event probability at most
**`42882m/p + 2 × bias`**, assuming the key has fifteen packed references. The theorem
allows any independent prior private-state law, including arbitrary row-mask samples.
It also bounds the event that a partial attempt completes with a zero denominator;
this is an unconditional event bound, not conditioning the law on completion.
[PlonkProductCertificate.lean](PlonkProductCertificate.lean) verifies in the kernel
that both captured keys have three permutation chunks and fifteen packed references.

[PlonkProductChallenges.lean](PlonkProductChallenges.lean) separates beta and gamma
exactly from the full wide-reduced challenge tape by commuting independent draws.
The other challenge coordinates retain their original wide-reduced laws, so this
separation adds no sampling error. It is an identity of the offline tape experiment,
not a claim about Fiat-Shamir outputs conditioned on a proof.

[PlonkRowPrerequisites.lean](PlonkRowPrerequisites.lean) names three
conditions: completed lookup construction, gate divisibility after masking, and the
packed copy-product identity. It proves that these conditions together with nonzero
denominators give exact numerator division on the same row tape.
[PlonkReferenceRowLaw.lean](PlonkReferenceRowLaw.lean) identifies the existing averaged
invalid-row term with that concrete tape experiment. Its union bound separates failure
of those prerequisites from the now-bounded denominator event.

[PlonkConstructedSimulation.lean](PlonkConstructedSimulation.lean) instantiates the
joint verifier-typed simulation with the concrete total reference constructors. Its
two-sided event bound is:

**`prerequisiteFailureMass + (42882m + 4113)/p + (148m + 70) × bias`**.

`prerequisiteFailureMass` is measured under the full wide-reduced challenge law and
independent uniform row tape already used in the sampling hybrid. It covers failed
construction, gates, or the copy-product identity. The original-row theorem below proves
it is zero under explicit witness and public-key conditions; connecting those conditions
to the full Action keygen remains open. Private row tapes appear only in the probability
analysis, not in the disclosed verifier view. No distribution is conditioned on success.

[ColumnRetained.lean](ColumnRetained.lean) and [PlonkAdviceRows.lean](PlonkAdviceRows.lean)
prove that every total-construction tape preserves the original usable advice cells,
including tapes whose partial construction later fails.
[PlonkPermutationMasking.lean](PlonkPermutationMasking.lean) carries this equality to
the computed permutation factors when their advice queries are unrotated.
[PlonkCopyCertificate.lean](PlonkCopyCertificate.lean) kernel-checks that public query
condition for both captured keys.

[CopyProducts.lean](CopyProducts.lean) propagates original copy equations through the
keygen replay's cycle closure. [PlonkCopyCells.lean](PlonkCopyCells.lean) identifies the
actual three-chunk numerator and denominator loops with products over typed usable
cells. [PlonkCopyWitness.lean](PlonkCopyWitness.lean) then derives their equality from
the original witness copy equations and public sigma coherence. This identity holds
for every challenge and row tape, including zero denominators; it does not require
cell-name injectivity or successful construction.

[PlonkCopyPrerequisites.lean](PlonkCopyPrerequisites.lean) proves that under those
explicit copy premises, `prerequisiteFailureMass` equals `gateConstructionFailureMass`.
[PlonkCopySimulation.lean](PlonkCopySimulation.lean) carries that exact equality into
the joint simulation bound:

**`gateConstructionFailureMass + (42882m + 4113)/p + (148m + 70) × bias`**.

This mass covers failed lookup construction or gate division after masking under the
original reference tape law. The original-witness theorem below proves it is zero
under explicit public mask conditions, without conditioning on success. This generic
endpoint takes a usable-cell copy list and its public sigma-label coherence as premises.
The compiler refinement below derives both. The copy-query certificates establish the
key's query layout.

[ExpressionMasking.lean](ExpressionMasking.lean) gives a computable, public expression
checker. It recognizes retained advice queries and products annihilated by fixed zero
selectors. Passing the check proves invariance under arbitrary changes to the other
advice values; failure of the check is not a claim that a mask actually influences the
expression. [PlonkAdviceRotations.lean](PlonkAdviceRotations.lean) connects the check to
the exact current, next, and previous query rows, including modular wraparound.
[PlonkExpressionRows.lean](PlonkExpressionRows.lean) identifies these expression values
with the existing polynomial gate and lookup-compression builders.

[PlonkOriginalRows.lean](PlonkOriginalRows.lean) separates original witness validity
from public mask safety. Original gates vanish and each uncompressed lookup input tuple
occurs in its table. The public mask profile then gives actual masked gate division
and compressed lookup membership for every challenge and tape.
[ColumnCompletion.lean](ColumnCompletion.lean) and
[PlonkLookupCompletion.lean](PlonkLookupCompletion.lean) show that the resulting successful
sorts make the actual partial column schedule complete on the same tape. This is
construction completion; zero product denominators can still affect proof acceptance.

[PlonkValidRows.lean](PlonkValidRows.lean) consequently proves that the construction-and-gate
failure mass is zero under any challenge law. With original copy equations and public
sigma coherence, all row prerequisites hold.
[PlonkOriginalSimulation.lean](PlonkOriginalSimulation.lean) gives the two-sided joint
reference-proof bound:

**`(42882m + 4113)/p + (148m + 70) × bias`**.

This removes the unbounded row term under the stated original-witness and public-key
premises. It does not assume uniform field masks or perfect completeness of the prover.

[PlonkMaskBoundary.lean](PlonkMaskBoundary.lean) reduces the public mask profile to eight
gate rows and two lookup rows: all advice queries in rows 1 through 2040 are retained.
[PlonkMaskCertificate.lean](PlonkMaskCertificate.lean) checks both captured keys in the
kernel using the stated fixed-query boundary values from `actionLayout.json`. The file
records the source hash and scalar values. Its profile theorems still require that
the supplied public polynomials evaluate to those values; authenticating the capture
and connecting these captured rows to full Action keygen remain open. The later compiler
copy and sigma refinement below derives those public copy profiles directly.
The product-coin experiment is now connected to the full independent challenge law.
Native-loop correspondence, including the
available Rust implementation's cancellation of fixed permutation cells on zero factors,
also remains open.

[KeygenFixedSupport.lean](KeygenFixedSupport.lean) proves a generic fact about the actual
`TopLevelCircuit` compiler: every raw fixed write is below the usable-row boundary.
Table default-fill stops at that boundary, while constants, selectors, and region writes
stay within the V1 placement. Deduplication and sorting preserve this support, and the
dense fixed columns are consequently zero on the masked suffix. This proof uses no
captured layout and has only Lean's standard axiom dependencies.

[PlonkPublicRows.lean](PlonkPublicRows.lean) constructs instance, fixed, and sigma
polynomials from their 2048-row vectors, proving every domain evaluation and degree
bound. [PlonkKeygenFixed.lean](PlonkKeygenFixed.lean) supplies the fixed vectors from
the compiler's dense columns. With domain exponent 11, five blinding rows, and at least
29 compiled fixed columns, the six masked boundary rows are proved zero. The remaining
finite check reads rows 0 and 2041 directly from the compiler; it does not assume an
equality between arbitrary public polynomial evaluations and captured scalar values.

`wideKeygenPlonkVerifier_simulation_error_bound` in
[PlonkKeygenSimulation.lean](PlonkKeygenSimulation.lean) uses this construction in the
same numerical joint bound. Its public degree premises are discharged, and its mask
profile follows from that finite compiler-row check. The instance and sigma vectors are
still supplied inputs, with original gate/lookup validity and copy equations required.
The selector refinement below narrows the remaining Action boundary check. The later sigma
refinement derives its rows from keygen. The later Action public-data and compiler-key
connectors supply statement provenance and public commitments. Concrete key shape,
query-layout, and expression checks remain open. The
existing Action compilation lemmas also carry the Pallas generator's native order
certificate; using them in an Action specialization requires explicit trust accounting.
The generic keygen endpoint is pinned without that dependency.

[PartialExpressionMasking.lean](PartialExpressionMasking.lean) lets a certificate leave
public fixed values unknown. A partial value or mask check refines the original checker
for every compatible full assignment; an unknown value cannot certify a zero factor.
[PlonkPartialMaskBoundary.lean](PlonkPartialMaskBoundary.lean) applies this to the same
eight gate and two lookup boundaries. The kernel certificates in
[PlonkSelectorCertificate.lean](PlonkSelectorCertificate.lean) pass for both captured
keys while leaving all fourteen original fixed columns unknown. At row 0 they require
only that packed-selector columns 18, 20, 21, and 24 are zero; the other selector values
there are unrestricted. At the later boundaries all fifteen packed-selector columns
are zero. No table element, generator coordinate, or region-fixed constant is needed.

[KeygenSelectorSupport.lean](KeygenSelectorSupport.lean) proves that packed-selector
writes come only from selector activations before V1's placement endpoint. Hence the
compiler's dense selector columns are zero afterward, even where table default-fill
continues through usable rows. The theorem also covers zero padding outside the compiler's
column and row ranges. [PlonkKeygenSelectors.lean](PlonkKeygenSelectors.lean) uses this
stronger support fact with the selector certificates: at most fourteen original fixed
columns, placement ending by row 2041, and the four initial packed-selector zeros suffice.
The former compiler-domain and fixed-column-count premises are unnecessary for this mask
profile and are removed from the positive simulation path. The reference prover still
has eleven IPA rounds and the verifier's 2048-row domain. The one- and two-Action profile
theorems use the actual captured expressions with these compiler fixed rows.

`wideSelectorKeygenPlonkVerifier_simulation_error_bound` in
[PlonkSelectorSimulation.lean](PlonkSelectorSimulation.lean) supplies this profile to the
numerical joint simulation, keeping the same bound. Establishing the four initial selector
zeros from the concrete Action compilation is still open; the captured row values alone
do not discharge that obligation. The Action specialization below supplies canonical
instance rows. The concrete key's shape, query layout, and expression conditions remain;
sigma rows and copy-list provenance are derived below.

[CopyReplayTransport.lean](CopyReplayTransport.lean) proves that an injective cell encoding
preserves the exact ordered copy replay, including its same-cycle test. This supplies the
usable-to-full-domain correspondence in [PlonkKeygenSigmaRows.lean](PlonkKeygenSigmaRows.lean).
Combined with the existing array/union-find assembly theorem, each entry of the compiler's
actual `permPolysOf` table is the delta/omega name of the corresponding replayed packed cell.

[PlonkKeygenSigma.lean](PlonkKeygenSigma.lean) interpolates these compiler rows into the public
sigma polynomials and derives their label-coherence equation. The original copy-value
equations are the only remaining copy-witness premise. [PlonkSigmaCertificate.lean](PlonkSigmaCertificate.lean)
checks the packed sigma indices, delta, and seven-column stride for both captured keys in
the kernel. These finite checks do not identify their full keys or public commitments
with compiled Action key generation.

`wideCompilerKeygenPlonkVerifier_simulation_error_bound` in
[PlonkCompilerSimulation.lean](PlonkCompilerSimulation.lean) retains the same two-sided bound
**`(42882m + 4113)/p + (148m + 70) × bias`** with fixed polynomials, sigma polynomials, and
the ordered copy list produced by the compiler. It takes neither arbitrary sigma rows nor
a separate sigma-coherence hypothesis. Original gate, lookup, and copy-value validity,
public size and expression certificates, the four initial selector zeros, and the URS
hiding condition remain explicit. The compiler-sigma no-perfect-simulator endpoint uses
the same public data in the unused-row witness argument.

### Verifier commitment routing

[PlonkCommitmentRouting.lean](PlonkCommitmentRouting.lean) connects the reference proof's
emitted private commitments to the existing verifier's `assembledCommitment` resolver.
The verifier's quotient MSM evaluates to the same weighted sum of the eight quotient
pieces as the reference prover. `PlonkPublicCommitmentsMatch` separately records the
required agreement of instance, fixed, and sigma commitments with the public polynomials.

`plonkVerifierGroup_commitmentMembers` uses the actual `constructIntermediateSets`
provenance theorem: every routed member carries the commitment named by its ID, including
when different slots happen to contain the same group value. `plonkCompressSet_commitment`
proves that reverse member order with ascending powers equals the prover's Horner fold,
for every batching challenge, including zero. Together these give
`plonkVerifierGroup_commitment`, whose group-order premise is now discharged by
`plonkVerifierGroup_commitment_from_layout` in
[PlonkVerifierGrouping.lean](PlonkVerifierGrouping.lean). The latter takes the key query
layout, distinct rotation points, a positive Action count, public commitment agreement,
and the 2048-row quotient convention. It derives every actual group ID list and the full
node order. The member-evaluation connection is completed below, followed by public
commitment agreement for compiler-derived keys. These connectors introduce no native certificate.

[PlonkQueryLayout.lean](PlonkQueryLayout.lean) proves the flat query stream for any Action
count under `PlonkQueryLayout`, which records the key's instance, advice, and fixed query
ordering and its five blinding rows. This stream equality includes exceptional challenge
values. Under injective interpretation of the four rotation labels, the actual verifier's
ID groups, node lists, and duplicate-query check agree with the finite pattern. The existing
five-point distinctness premise implies that injectivity.
[GroupingPattern.lean](GroupingPattern.lean) proves the transport without assumptions on
commitment values or claimed evaluations.

[PlonkQueryBlocks.lean](PlonkQueryBlocks.lean) derives the first-appearance commitment order
by composing disjoint Action blocks with the shared suffix. Only the fixed local layout is
kernel-evaluated; the theorem applies to arbitrary bundle sizes. Every positive Action count
has the same four-point table. [GroupingSlots.lean](GroupingSlots.lean) projects the existing
algorithm to slot order and point-index sets, including its reversal before routing.
[PlonkQueryGroups.lean](PlonkQueryGroups.lean) completes the slot classification and proves
that the resulting five filtered lists are exactly the reference opening lists, with
the verifier's reversal. The theorem covers all positive Action counts, independently
of the IPA round count. [PlonkQueryCertificate.lean](PlonkQueryCertificate.lean) checks the
layout premises for both captured keys; it does not certify their commitment values.

[PlonkQueryUniqueness.lean](PlonkQueryUniqueness.lean) proves that slot/rotation pairs never
repeat, for any Action count. Under injective point interpretation, the actual duplicate
guard succeeds. [PlonkQueryClaims.lean](PlonkQueryClaims.lean) identifies every flat scalar
claim with the reference view, using the verifier's existing inferred quotient value for
the `H` slot. This flat-stream equality also covers exceptional challenges.
[PlonkEvaluationRouting.lean](PlonkEvaluationRouting.lean) then derives each routed
member evaluation; query membership and routed-ID agreement are not additional premises.

`plonkVerifierGroup_evaluations_from_layout` in
[PlonkEvaluationCompression.lean](PlonkEvaluationCompression.lean) proves equality of the
complete compressed evaluation vectors with `plonkPublicNodeValues`. The proof establishes
their lengths, node indices, and the reversal between the verifier's ascending powers and
the reference Horner fold. It applies to every batching challenge, including zero, under
the same positive Action count, query-layout, and distinct rotation-point conditions.
It does not require public commitment agreement for the scalar-vector equality.

[PlonkCompressedGroups.lean](PlonkCompressedGroups.lean) assembles these results into the
actual five-entry compression table: zipping retains every group, and both projections
match the complete reference lists. [MultiopenAssembly.lean](MultiopenAssembly.lean) proves
that the final combination depends on its input MSMs only through their evaluated points.
`plonkVerifierOpening_eq_public` in [PlonkVerifierOpening.lean](PlonkVerifierOpening.lean)
then connects the actual `assembleOpening` result to `plonkPublicOpening`. The commitment
point and scalar agree, even though the intermediate MSM representations can differ.
The theorem uses the key layout, a positive Action count, distinct rotation points,
public commitment agreement, and the reference domain size and root. It imposes no
nonzero batching-challenge condition. The dynamic group-count check is also proved to
succeed. These connectors do not assert verifier acceptance or alter the simulation bound.

[PlonkKeygenCommitments.lean](PlonkKeygenCommitments.lean) connects the compiler's actual
Lagrange commitments to the reference row interpolants, including the public blind of one.
It uses the existing FFT and commitment correctness lemmas. The primitive-root proof is
now shared from [Arithmetic/Domain.lean](../../Arithmetic/Domain.lean): the same kernel-checked
modular exponentiations support both the compiler and ZK layers, without the former native
root-certificate dependency.

`plonkCompilerPublicCommitmentsMatch` in [PlonkDerivedKey.lean](PlonkDerivedKey.lean) derives
all instance, fixed, and sigma commitment equalities for `TopLevelCircuit.toVerifierKey`.
The query layout guarantees all 29 fixed columns exist; the circuit shape supplies the
15 sigma columns. Its key transport changes only the type-level circuit dimensions.
`plonkCompilerOpening_eq_public` applies the complete opening connector to that generated
key and derives the reference domain size and root too. It requires shape and query-layout
agreement, eleven IPA rounds, a positive Action count, and distinct rotation points;
it has no separate public-commitment or domain-value premise. Action's configuration
theorems now supply the compiled shape and query layout given fifteen compressed
selector columns. That compression count still needs a source certificate.

### Actual Action public data

[ActionPublicData.lean](ActionPublicData.lean) fixes the circuit to `actionCircuit`.
`actionInstanceRows` reads its actual public-input layout, and the instance-polynomial
theorem proves equality with the canonical public-input element vector at every domain
row. `actionPublicPolynomials` combines those rows with the compiler's fixed and sigma
rows. The masking profiles for both captured keys now use those public polynomials.
Action's already-proved fourteen-column prefix and placement endpoint 1779 supply the
general selector-support premises. `ActionInitialSelectorsZero` names the four
initial-row facts used by the older selector-only route; it remains an unproved
proposition, but the main compiler theorem no longer requires it.

`wideActionReference_simulation_error_bound` in [ActionSimulation.lean](ActionSimulation.lean)
applies the encoded Vesta comparison to this Action public data and its compiler copy list.
The existing fifteen-column permutation and exact operation-footprint theorems discharge
the corresponding compiler conditions. The error bound is unchanged. Original gate,
lookup, and copy-value validity, the four initial selector zeros, the remaining key
expression/layout conditions, and nonidentity of the blinding point are explicit.
The captured nonidentity lemmas above supply the latter for all four URS fixtures.
The public simulator takes these public inputs and has no witness argument.

The stronger `wideActionCompilerReference_simulation_error_bound` in
[ActionCompilerSimulation.lean](ActionCompilerSimulation.lean) obtains the complete
degree and masking profiles from the actual Action compiler. In particular,
[ActionBoundaryProfile.lean](ActionBoundaryProfile.lean) proves that the boundary
check holds using the actual fixed values. The source trace excludes every guard
of a previous-row read from row zero. Compression preserves that guard's zero value
even when another selector in the same column is active. The partial expression
checker evaluates these public factors, and its compiler-preservation proof carries
them through all gates and lookup expressions. The exact source-sort, placement,
activation-bit, and greedy-packing certificates now prove the fifteen-column count.
The encoded comparison therefore needs no initial-column-zero, selector-routing,
or compression-count premise.

[ActionCommitments.lean](ActionCommitments.lean) identifies Action's existing public data
with the general compiler construction. Its actual public-input and sigma commitments
agree with the reference polynomials using Action's proved domain and permutation count.
`actionCompilerPublicCommitmentsMatch` supplies all public commitment equalities, and
`actionCompilerOpening_eq_public` supplies the final opening equality, for Action's
compiler-derived key under the stated shape and query-layout premises. They do not
assume equalities of the captured commitment bytes.

[Action/TrustBoundary.lean](Action/TrustBoundary.lean) names the existing
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt` dependency carried by the opaque Action circuit
package, alongside the Vesta order dependency of the concrete simulation. This refinement
introduces no new native certificate and does not assert the initial selector zeros.

[PlonkBinaryBounds.lean](PlonkBinaryBounds.lean) proves the simpler numerical statement
**`epsilon(m) < m * 2^-238` for `m >= 1`**. It uses the proved `bias <= 2^-260` and
kernel-checked integer arithmetic for one Action, then the affine dependence on `m`.
The coefficient `148m+70` counts bias costs in the comparison: `148m+46` private samples,
22 verifier-challenge costs, and two additional costs in the exceptional-event analysis.
Those last two costs do not add random draws to the prover tape.

The main Action reference theorem now derives its concrete circuit and key properties
from the source compiler. Its witness premise is satisfaction of the original gates,
lookup tuples, and compiler copy equations; its public-parameter premise is a nonzero
blinding point in the eleven-round setup. The group IDs, node order, duplicate guard,
commitment compression, complete evaluation vectors, and final opening assembly follow
under the stated distinct-point condition. Public commitment agreement, domain values,
shape, layout, and the complete degree and masking profiles are supplied by Action key
generation and the checked compression count. Exceptional challenges remain in the
simulation experiment and are charged to its numerical error bound.
The complete reference computation has
a checked stage-by-stage causality proof on the same private tape and sampling law. The
successful single-attempt law and the unlimited independent retry-history law are now
normalized. Exact finite projections, vanishing exhaustion tails, expected-attempt bounds,
and the full unlimited-history comparison are proved for the closed Action construction.
The attempt observation above now retains the scheduled failures and partial output.
Its random-bit tape and independent verifier
challenges are explicit assumptions of the interactive experiment.

The [one-attempt Fiat–Shamir theorem](ActionFiatShamir.lean) supplies the separate
classical random-oracle simulation argument and its `epsilon(m) + q_pre / p` bound.
A theorem about a particular executable would additionally require implementation correspondence;
the available Rust quotient implementations have not been proved equivalent to these
polynomial computations. Neither whole-program Rust parity nor a concrete PRNG proof is
a prerequisite for the protocol-level statistical HVZK target.

## Checks

The following checks the proofs, declared transitive axiom dependencies, and endpoint coverage:

```sh
lake build --wfail Zcash.Snark.ZeroKnowledge.TrustBoundary \
  Zcash.Snark.ZeroKnowledge.Vesta.TrustBoundary \
  Zcash.Snark.ZeroKnowledge.Action.TrustBoundary CensusCheck
```

The parent census permits only Lean's standard axioms. The concrete Vesta and Action
censuses name their inherited curve-order certificates separately. The sampling program,
canonical observer, and Action public-data construction are also pinned as computable.
This directory is included in the default library build, and all three trust boundaries
are imported by `CensusCheck`.

The [complete Action advice source](ActionAdviceSourceData.lean),
[gate activations](ActionGateSourceCertificate.lean), and
[lookup activations](ActionLookupSourceCertificate.lean) now have checked source
certificates. They preserve 18,403 witness instructions, 4,058 gate entries, and
2,424 lookup entries. This supplies the original data for the remaining global
witness-execution and activation-coverage checks.

The [read-address factorization](AdviceReadAddressScan.lean) lets the checker
normalize source-owned placement data before evaluating the unchanged read
policy. The original problematic Action entries and adversarial opaque-source
regressions pass; the full Action read/alias scans remain separate checks.

The [complete proof-field routes](RoutedProofCost.lean) now retain all producer
prices, including query-table searches and permutation/lookup record preparation.
The [counted transcript](TranscriptScheduleCost.lean) erases to the original full
message schedule. At eleven IPA rounds its
[cost bound](TranscriptScheduleBound.lean) is
`8m^2 + (72m + 85)R + 1300m + 2200`, where `R` bounds every field's complete
producer. This includes optional claims and all final responses, even when later
observation stops early. Whole-simulator and oracle-observer composition remain
separate runtime steps at that checkpoint; these structural costs do not change
the statistical simulation error.

The [stored-joint proof constructor](StoredJointProofCost.lean) now feeds that
schedule directly. Its [complete tape-to-transcript theorem](StoredActionTapeTraceCost.lean)
recovers the original flat-tape simulator, and its [fixed bound](StoredActionTapeTraceBound.lean)
derives all reader prices and generated dimensions. Canonical observation and
[pre-challenge reports](CanonicalOracleReportCost.lean) include every actual
codec and failure check. [Query-address construction](QueryAddressCost.lean)
counts all prefix copies and encoded bytes. The [raw reply reader](StoredDigestPrefixCost.lean)
exposes exactly the zero-extended public prefix, preserving its agreement with
the reduced challenges while keeping the private suffix internal.
