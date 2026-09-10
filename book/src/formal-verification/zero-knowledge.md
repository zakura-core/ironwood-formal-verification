# Zero knowledge and executable reductions

The zero-knowledge development compares the specified honest prover with a
simulator that receives public inputs and setup parameters. The Action
application theorem constructs the prover's rows from
`ActionWitnessConstructionConditions`, which includes `ActionSpec`, defined
hashes, canonical encodings, and scalar-hint bounds. The one-attempt interactive
comparison uses independent uniform input bits and a nonidentity blinding point.

Fiat–Shamir comparisons use a programmable classical random oracle. Retry and
continuing-generator results state their own fixed-request, stopping, and PRNG
test-class premises. Concrete BLAKE2b security, security of a particular PRNG,
and whole-program Rust correspondence are separate claims. The
[Action witness theorem statements](https://github.com/zakura-core/ironwood-formal-verification/blob/859e54eac7c973238ec25c0b50b42264747aadce/Zcash/Snark/ZeroKnowledge/ActionWitnessSimulation.lean)
give the precise application contract.

## Computability boundary

The operational reduction programs are ordinary Lean definitions with
`assert_computable` pins. `ActionReductionProgram.evalCosted` and
`InteractiveReductionProgram.evalCosted` consume stored inputs and random bits,
produce a Boolean observation, and retain execution counters. Their erasure and
cost theorems connect those computations to the security games; an abstract
probability kernel alone does not supply an executable reduction. See the
[program interfaces and resource model](https://github.com/zakura-core/ironwood-formal-verification/blob/859e54eac7c973238ec25c0b50b42264747aadce/Zcash/Snark/ZeroKnowledge/PROGRAMS.md).

The following proof-side objects retain `noncomputable` declarations:

| Objects | Why the marker remains | Where they are used |
| --- | --- | --- |
| Sampling laws, event masses, error bounds, retry measures, and PRNG kernels | `PMF`, measure, and extended-real operations describe mathematical probabilities. In particular, `ActionReductionProgram.kernel`, `InteractiveReductionProgram.kernel`, and `tapeReduction` are laws of computations, not implementations of a random-bit source. | Distribution equalities, probability bounds, and admissibility predicates. |
| Masking equivalences, linear maps, and finite enumerations | The algebraic proofs use inverse maps and finite-type constructions supplied through choice. The `CommitmentMask`, `IpaSimulation`, `RowMaskRank`, and `PlonkFiniteView` modules own these objects. | Coupling, rank, and finite-distribution proofs; the operational programs do not execute these choice-based constructions. |
| Action source certificates and scan continuations | Expanded source programs and stored scan maps can contain auxiliary definitions intended only for kernel reduction. Code generation is disabled for these static certificate values. | Proofs of source erasure, read availability, alias validity, and activation coverage. |

The static Action values are `actionAdviceSourcePrefix`, `actionAdviceSourceCertificateRaw`,
`actionAdviceSourceCertificate`, `actionGateSourcePrefix`, `actionGateSourceCertificateRaw`,
`actionGateActivationSourceCertificate`, `actionLookupSourceCertificateRaw`,
`actionLookupActivationSourceCertificate`, `actionWitnessLoadSourceCertificate`,
and `actionValueSourceCertificate`. Their retained data are checked against the
original programs; they are not witness constructors or security-reduction
outputs. The noncomputable source-certificate values in `Zcash.Meta.Tests` serve
the same purpose in positive and negative regression cases.

The `ActionAdviceSourceChunks`, `ActionGateSourceChunks`, and
`ActionLookupSourceChunks` modules contain further static continuations. Each
module checks source pieces and retains the remaining source; successive modules
compose their continuations.
`ActionAdviceSourceData`, `ActionGateSourceCertificate`, and
`ActionLookupSourceCertificate` close the corresponding chains. Each final
certificate requires the remaining source to be empty.

The private `SourceCertificatePiece` values used to assemble these certificates
are static proof artifacts as well. Each piece retains its exact remaining
source and a kernel-checked continuation. Closing the complete certificate
requires a certificate for that remainder; an empty certificate can close only
an empty remainder. Each piece is elaborated under the default heartbeat limit.

`AdviceMapScanPiece` also carries the remaining alias map. Its continuation
requires the scan to succeed from that map and the remaining entries. The source
and map pieces serve the proof of the original complete checks.
The `ActionAdviceAliasChunks` and `ActionAdviceReadChunks` modules retain these
static map states and compose the corresponding scan continuations.
`ActionAdviceSourceAliasCheck` and `ActionAdviceReadPlan` prove that their final
remainders are empty before using the continuations to establish the complete
alias and read checks.

Activation metadata normalized by `certify_coverage_data` is stored in exact
source-list certificates. `CoverageTreePiece` retains each accumulated comparison
tree and requires the remaining fold to produce the claimed final tree. These
metadata and tree values also serve only the static coverage proofs and their
regression tests. `ActionCoverageData` owns the shared selector activations;
`ActionGateCoverageData` and `ActionLookupCoverageData` own the configured
registries and source labels. Their corresponding `CoverageTree` modules
require empty source remainders before checking the configured predicates.
`ActionGateActivationCoverage` and `ActionLookupActivationCoverage` transport
those results back to the original Action circuit metadata.

`ActionWitnessRows` owns the executable application witness constructor.
`ActionWitnessSimulation` uses the static certificates only to prove that its
output satisfies the relation required by the simulation theorems. Executable
finite-tape simulators and their probability laws are likewise separate
declarations. Replacing a proof-side object with an operational producer requires
a computability pin and an update to this boundary.
