# ZK review packet

Proof baseline: `15fe03fbd72e478601660067065fea711ce17552` on `establish-zk` in
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
the simulation results provide both directions. The PRNG results instead bound
the Boolean output of an admitted test under an explicit security assumption.

| Claim | Theorem and source | Compared laws |
| --- | --- | --- |
| One complete interactive Action attempt, error `epsilon(m)` | `wideActionZkRelation_simulation_error_bound` in [ActionInstantiation.lean](ActionInstantiation.lean), using [the actual compiler theorem](ActionCompilerSimulation.lean) | `actionZkProver` and `actionZkSimulator` |
| Unlimited independent interactive retries, error `epsilon(m)/(1-F(m))` | `wideUnlimitedActionZk_simulation_error_bound` in [ActionRetryLimit.lean](ActionRetryLimit.lean) | `actionZkRetryProver` and `actionZkRetrySimulator` |
| One-attempt programmable-oracle simulation, error `epsilon(m)+q_pre/p` | `actionFiatShamir_simulation_error_bound` in [ActionFiatShamir.lean](ActionFiatShamir.lean) | `actionOracleRealExperiment` and `actionOracleSimulatedExperiment` |
| One-attempt fixed-bit simulator, error `epsilon_bits(m,q_pre)` | `actionFiatShamirBits_simulation_error_bound` in [ActionFiatShamirBits.lean](ActionFiatShamirBits.lean) | `actionOracleRealExperiment` and `actionOracleBitSimulatedExperiment` |
| Every finite shared-oracle retry budget, error `R(m,q_pre,n)` | `actionFiatShamirRetry_simulation_error_bound` in [ActionFiatShamirRetry.lean](ActionFiatShamirRetry.lean) | `actionOracleRetryRealExperiment` and `actionOracleRetrySimulatedExperiment` |
| One seeded interactive attempt, test error `epsilon(m)+eta` | `uniformSeedActionZk_test_error_bound` in [ActionPrngSecurity.lean](ActionPrngSecurity.lean) | Auxiliary-data mixtures of tested `actionZkProverFromSource` and `actionZkSimulator` |
| Finite retries from one continuing generator, test error `R(m,q_pre,n)+eta` | `generatedActionFiatShamirRetry_test_error_bound` in [ActionGeneratorPrng.lean](ActionGeneratorPrng.lean) | Tested `actionGeneratedOracleRetryExperiment` and `actionOracleRetrySimulatedExperiment` |

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
  is a checked sufficient condition, not a protocol maximum. Shared-oracle
  retries have a finite theorem only. Its bound grows with the budget and supplies
  neither an unlimited history law nor almost-sure shared-oracle termination.
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
```

`F` bounds failure to finish the emission schedule and hence the retry probability.
Finishing that schedule does not assert verifier acceptance. The binary certificates
are in [PlonkBinaryBounds.lean](PlonkBinaryBounds.lean),
[OracleBitBounds.lean](OracleBitBounds.lean), and [OracleRetryBounds.lean](OracleRetryBounds.lean).

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

**Validation and review status**

The [validation record](review/validation-15fe03fb.log) contains the successful
full default-target build (`lake build --wfail`, 4,258 jobs), repository guards,
and the [46-declaration dependency inventory](review/axioms-15fe03fb.log) for the
latest proof milestone. All 818 modules are covered by default targets and all
308 endpoint declarations are pinned. The full [parent](TrustBoundary.lean) and
[Action](Action/TrustBoundary.lean) boundaries also check the earlier milestones.
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
whether future efficiency or unlimited-run claims add the required proofs.
