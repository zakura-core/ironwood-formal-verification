# Independent ZK review record

Three separate AI review agents completed the review on 2026-09-10 UTC. Each
reported no blocking finding within its assigned scope and no required source
change. This completes the checklist's final review item. The completed checklist
has been removed; the [review packet](../REVIEW.md) retains the theorem map,
assumptions, bounds, and validation history.

Reviewed HEAD: `469ad6bb782329f632713f25b814f515b53f89ba`.
Proof-source baseline: `4a87136b23e7b25eb079a19e7f1289838f138dc1`.
All Lean sources, toolchain, and dependency inputs were unchanged between these
revisions. The reviewers made no tracked edits. This record describes separate
AI-agent review passes, not a human third-party audit or a GitHub approval.

| Reviewer | Assigned scope | Result | Fresh checks |
| --- | --- | --- | --- |
| `/root/interactive_review`, `zk_researcher` | Interactive ZK, joint masks, sampling, and application Action witnesses | No blocking findings; slice can close | 9 kernel probes, 25 source axiom queries, exact sampling arithmetic |
| `/root/oracle_review`, `soundness_auditor` | Fiat–Shamir, retained retries, complete oracle and continuing-generator streams | No blocking findings; slice can close | 12 kernel probes, 16 source axiom queries |
| `/root/resource_review`, `crypto_code_reviewer` | Complete prover/simulator costs, concrete tests, and operational PRNG reductions | No blocking findings; slice can close | 6 kernel probes, all 164 declarations and 29 module imports reconciled |

**Interactive protocol and application witnesses**

The review traced the comparison from the actual reference prover to the
public-input simulator in [ActionInstantiation](../ActionInstantiation.lean#L41),
the key constructed by [the actual Action compiler](../ActionDerivedKey.lean#L51),
and [the fixed-tape law equality](../PlonkEncoding.lean#L49). The
[compiler theorem](../ActionCompilerSimulation.lean#L88) discharges domain,
layout, degree, masking, and blinding conditions; its opening and commitment
routing uses the actual key. The [application bridge](../ActionWitnessSimulation.lean#L17)
composes generated witness equations, original Action completeness, and the
gate/lookup/copy bridges. The remaining caller contract is explicit in
[ActionWitnessConditions](../ActionWitnessConditions.lean#L24).

The [joint simulation](../PlonkComposition.lean#L127) preserves the shared private
material and inherited IPA blind. It does not substitute an independence
assumption between PLONK and IPA. The sparse evaluation-direction case is a
[public zero](../SparseIpa.lean#L133), and the
[two-evaluation linear-mask argument](../LinearMask.lean#L23) requires distinct
points. Domain hits and zero xi remain permitted; the
[attempt observer](../PlonkAttempt.lean#L42) preserves stopping order, emitted
prefixes, and received challenges. Their exceptional probability and the actual
wide-reduction law are charged in the statistical comparison.

The private tape contributes `148m + 46` samples; the additional public-challenge
and denominator comparisons give the final `(148m + 70) delta` coefficient in
[PlonkConstructedSimulation](../PlonkConstructedSimulation.lean#L50). Independent
exact arithmetic confirmed `delta <= 2^-260` and `epsilon(1) < 2^-238`. The review
also cross-checked the pinned prover description's masks, IPA equation, encoding,
and failure policy against these sources.

**Oracle simulation and complete retry histories**

The review traced all 22 challenges through the
[verifier's byte schedule](../PlonkQuerySchedule.lean#L82) and
[causal replay](../PlonkOracle.lean#L87), including exceptional executions.
[Cache programming](../OracleProgramming.lean#L19) preserves existing answers
and refuses prior addresses. The [privacy reduction](../ActionOracleAdversary.lean#L75)
erases the selected witness while preserving auxiliary state and the shared cache.

[Retries](../OracleRetry.lean#L17) continue only on `retryRandomness`. Completion,
coincident openings, and programming failure stop; zero budget is exhaustion.
The finite and complete-stream laws preserve prefixes, statuses, and caches.
[Exact prefix laws](../StatefulRetryStreamLaw.lean#L119) and the
[measure extension](../MeasureStreamLimit.lean#L17) transfer the uniform finite
bound to measurable stream events. The real nontermination mass is bounded,
rather than removed by conditioning.

The [continuing-generator stream](../GeneratedRetryStreamTail.lean#L84) samples
one seed and independent public replies. Its
[PRNG theorem](../ActionGeneratorStreamPrng.lean#L74) uses both the clipped-view
and exhaustion reductions, with error `2(C + b^n + eta)`. It assumes neither
independent generated blocks nor termination for every seed. The
[operational corollary](../CostedActionGeneratorStream.lean#L13) supplies
measurability and both reductions' membership at their common maximum budget.

**Runtime and operational PRNG reductions**

The reviewer read all 29 inventoried modules and traced their composition through
the complete real prover, observer, cache execution, retained retries, and
simulator. The [recorded](../ActionReductionProgram.lean#L17) and
[interactive](../InteractiveReductionProgram.lean#L17) classes accept concrete
finite Boolean programs and composition. They include ordinary raw-tape tests;
they cannot accept an arbitrary host function with an asserted counter.

[Complete reduction costs](../ObservedReductionCost.lean#L29) include auxiliary
copying, actual proving, canonical observation, cache searches and growth,
retained retry records, and circuit reads. The
[per-candidate law](../StoredActionRecordedBitsLaw.lean#L10) retains the actual
private tape, including correlated PRNG prefixes. The
[interactive encoding](../InteractiveViewEncoding.lean#L7) is injective and
retains the full verifier challenge tape. The
[recorded readers](../RecordedTestRead.lean#L22) distinguish absent data,
programming failure, present zero, intermediate and final caches, and exhaustion.

The [interactive](../InteractiveReductionSource.lean#L35) and
[recorded](../ActionReductionSource.lean#L59) bridges identify the original
PRNG reductions and prove their actual class membership. The
[complete simulator bound](../StoredActionOracleSimulatorBound.lean#L24) and
[exact law equality](../StoredActionOracleRuntime.lean#L36) concern the same
simulator used by the statistical theorem.

**Validation and reproducibility**

All four independent Lean invocations used `-DwarningAsError=true` and exited 0.
Their exact commands, hashes, counts, reviewers, and verdicts are in the
[manifest](independent-469ad6bb/manifest.json). Diagnostic sources are stored as
`.lean.txt` so they do not silently add modules to the production build surface.

| Diagnostic | Retained source | Raw output |
| --- | --- | --- |
| Interactive boundaries and dependencies | [Source](independent-469ad6bb/interactive.lean.txt) | [Log](independent-469ad6bb/interactive.log) |
| Oracle, retry, and stream boundaries | [Source](independent-469ad6bb/oracle.lean.txt) | [Log](independent-469ad6bb/oracle.log) |
| Complete resource dependency inventory | [Source](independent-469ad6bb/resource-axioms.lean.txt) | [Log](independent-469ad6bb/resource-axioms.log) |
| Cache, retry, raw-bit, and membership edges | [Source](independent-469ad6bb/resource-edges.lean.txt) | [Log](independent-469ad6bb/resource-edges.log), empty on success |

The 27 kernel probes cover exceptional challenges and stopping order, retained
failure prefixes, mask degeneracies, retry exhaustion and terminal outcomes,
cache conflict and first-match behavior, reply-slot advancement on cache hits,
nonterminating streams, continuing-generator advancement, raw bit 511, and
ordinary raw-circuit membership. The resource scan exactly reproduced all 164
recorded axiom sets and all direct pins/imports. The generic boundary has no
native exemption. Across the final logs, only standard Lean axioms and the two
already documented Pasta order certificate owners occurred. The root agent
independently reconciled the final log counts and permitted axiom sets.

The final oracle and resource-edge probes passed after correcting temporary
harness tuple-annotation and missing-`DecidableEq` errors. These were diagnostic
edits, with no repository proof change. To replay the final probes from the
repository root:

```sh
set -eu
review_scratch="$(mktemp -d "${TMPDIR:-/tmp}/ironwood-independent-review.XXXXXX")"
for probe in interactive oracle resource-axioms resource-edges; do
  cp "Zcash/Snark/ZeroKnowledge/review/independent-469ad6bb/$probe.lean.txt" "$review_scratch/$probe.lean"
  lake env lean -DwarningAsError=true "$review_scratch/$probe.lean"
done
```

The [exact arithmetic record](independent-469ad6bb/sampling.json) is reproducible
without floating-point comparisons:

```python
from fractions import Fraction
p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
Q, r = divmod(2**512, p)
delta = Fraction(r * (p - r), p * 2**512)
epsilon1 = Fraction(42882 + 4113, p) + (148 + 70) * delta
assert delta <= Fraction(1, 2**260)
assert epsilon1 < Fraction(1, 2**238)
```

The unchanged proof baseline already passed the
[complete 4,858-job build and repository guards](validation-4a87136b.log), with
[raw output](build-4a87136b.log) and the
[declaration inventory](declarations-4a87136b.json). The full build was not
repeated for this documentation closure. Historical validation records preserve
their original dates and pending-work statements.

**Retained qualifications**

The interactive claim is statistical HVZK for the specified reference experiment
with the stated witness/setup contract and independent uniform raw tapes. The
Fiat–Shamir claim uses a classical programmable random oracle. Complete stream
results keep a fixed request and initial cache, without intervening adversary
queries; adaptive before/after oracle phases are covered by finite experiments.
Seeded results retain the explicit PRNG-security assumption.

The closed runtime items concern supplied materialized inputs and finite circuits
in the [structural primitive-cost model](../PROGRAMS.md). Generic probabilistic
tests and adaptive preprocessing/postprocessing retain explicit admissibility
premises. Runtime bounds begin with materialized inputs and exclude the cost of
setup/key/witness generation. This review does not establish machine-time or Rust
correspondence, concrete BLAKE2b security, malicious-verifier ZK, perfect ZK,
knowledge soundness, or historical priority. These scope limits remain recorded
after checklist removal; no unresolved review finding remains.
