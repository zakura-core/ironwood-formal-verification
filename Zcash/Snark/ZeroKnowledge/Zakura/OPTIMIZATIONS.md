# Source review of optimized computation

The release mask equations agree with the reference description: the IPA mask
is `Σ a_t (X^(2^t) − q^(2^t))`, and the separate multi-opening mask is
`r(X) = a + bX`. The [provenance record](PROVENANCE.md) identifies the exact
sources. Agreement of these equations and an unchanged circuit do not by
themselves establish the optimized prover's full joint output law.

The source review covers the following five paths and their randomness order.
Here, source review means manually comparing the pinned Rust code with the
Lean definitions. It records the implementation correspondence assumption;
it does not prove equality of the Rust and Lean output distributions.
The listed tests exist in Common `50f712ee22ca95e2dd5230c6f331ce2e433d70ee`;
they provide optional implementation evidence, not premises of the Lean ZK
theorem. The preparation script selects them by their exact Rust test names.
Listing a test is not evidence that it has run, and a passing regression
establishes only the cases that it executes.

| Path | Reference behavior | Source review and optional test evidence |
| --- | --- | --- |
| Parallel synthesis and blinding | Preserve each witness row, the ordered association of independent random samples with columns and blinds, and transcript emission order. Prepared Merkle synthesis must supply the same circuit rows. | Lean [ActionCompilerSimulation](../ActionCompilerSimulation.lean) and [RawFieldTape](../RawFieldTape.lean); Rust [prover](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs). Tests `parallel_advice_evaluation_preserves_proof_bytes`, `instance_preparation_preserves_proofs_and_validates_batch_first`, `instance_failures_do_not_run_synthesis_or_consume_rng`, `v1_proving_key_reuses_floor_plan`, and Orchard single-worker/multiple-Action proof tests. |
| Lookup sorting and commitment reuse | Produce the reference permutation, including repeated/zero values, and preserve `C(input,r_i) = C(table,r_t) + C(input − table,r_i − r_t)` as a joint commitment computation. | Lean [LookupSort](../LookupSort.lean), [PlonkConstructedLookup](../PlonkConstructedLookup.lean); Rust [lookup prover](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/lookup/prover.rs). Tests `sorted_lookup_permutation_matches_reference_exhaustively`, `sorted_lookup_permutation_preserves_output_order`, `sorted_lookup_permutation_rejects_missing_value`, `table_sort_matches_field_order`, `permuted_pair_commitments_reuse_table_vesta`, and `sorted_u10_commitment_matches_lagrange_vesta`. |
| Grand products | Preserve the ordered prefix products, including zero numerators and denominators, and leave the blinded rows untouched. A nonzero-only aggregate inverse identity is insufficient. | Lean [PlonkConstructedPermutation](../PlonkConstructedPermutation.lean), [PlonkLookupRows](../PlonkLookupRows.lean); Rust [prefix-product helper](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk.rs#L58). Tests in `prefix_products_of_fractions_tests` compare the aggregate inversion and its zero-aware branch against the reference, including bitmasks and full-length zero patterns. |
| Quotient planning and multi-opening | Preserve constraint-polynomial evaluation, quotient pieces, challenge power order, and the synthetic-division result. Cached plans must match the circuit count and polynomial tags. At an opening-node collision, evaluate the released quotient fallback without resampling. | Lean [QuotientPieces](../QuotientPieces.lean), [PlonkMultiopen](../PlonkMultiopen.lean), [MultiopenPolynomial](../MultiopenPolynomial.lean); Rust [cached prover plan](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/plonk/prover.rs#L1460), [multi-opening](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/poly/multiopen/prover.rs#L660). Tests `compressed_selector_cache_preserves_proof` (cold, warm, incompatible and concurrent plans), `parallel_q_prime_matches_ordered_operator_fold_fp`, `parallel_evaluations_match_serial_order_fp`, `zero_challenge_selects_last_polynomial_fp`, and `in_place_kate_division_matches_allocating_fp`. |
| IPA, deferred arithmetic, and MSM | Preserve sparse-mask sampling, commitment bases/blinds, each `L/R` pair, folding scalar, and final encoding. Zero IPA challenges must panic after the same prefix; identity points must fail before receiving the next challenge. | Lean [IpaProver](../IpaProver.lean), [IpaAttempt](../IpaAttempt.lean); Rust [IPA prover](https://github.com/zakura-core/common/blob/50f712ee22ca95e2dd5230c6f331ce2e433d70ee/crates/halo2_proofs/src/poly/commitment/prover.rs). Tests compare prepared/unprepared proof bytes, compact/eager folds, sparse-mask commitments and masking bases, and deferred/native Vesta arithmetic. Run on portable and aarch64 assembly profiles. |

## Implementation evidence and trust boundary

The Lean endpoint compares the released API observation of a reference
computation. Refreshing the existing verifier fixture formats from the pinned
release and reviewing the changed prover source retain the implementation
connection used by the earlier result. Universal Rust-to-Lean correspondence
remains an explicit trust boundary. New RNG/trace instrumentation and a universal
equivalence proof are outside this task.

The [fixture preparation](../../../../scripts/prepare_zakura_release.py) invokes
the release's existing exporters without Rust source changes. These compare
sampled verifier executions with Lean; they do not establish the prover's
randomness law. The zero-knowledge theorem compares distributions of the Lean
prover model. Identifying that model with the Rust prover remains the documented
implementation assumption.

The reference IPA input now uses the final polynomial's actual evaluation at
all points, including opening-node collisions. The costed computation uses
the same value through stored-coefficient Horner evaluation. The
[collision regression](MultiopenRegression.lean) distinguishes it from the
verifier's totalized division; the existing simulation uses their proved
agreement away from opening nodes. These Lean changes await elaboration.

The optional prepared regressions cover serial/default features, one/four worker
settings, single/multiple Actions, and cache behavior already exercised by the
release's tests. They do not establish arbitrary scheduler equivalence,
constant-time behavior, concrete PRNG security, or BLAKE2b's random-oracle
assumption. The optional `orbits` and unstable voting-circuit features are
outside the recorded release profile.
