# Zero-knowledge formalization

This development starts from the [pinned prover description](https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md),
on Ironwood base `ad4a6ad8f75a64368bae4186006480410a687cce`. The description names Sensei
`56a7de7`; that implementation commit has not yet been located. These are proofs about the
specified constructions, not a verified correspondence with that Rust executable.

There is not yet a zero-knowledge theorem for the complete prover. The existing verifier and
soundness formalization does not supply an honest-prover distribution or simulator.

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
not condition on success. The description's declared count is `148m + 46` field samples
for `m` Actions, or 1,552 / 2,736 64-bit words for one / two Actions. Instantiating the
continuation with a fully modeled prover and verifying that count against Rust remain open.

## Checks

`lake build Zcash.Snark.ZeroKnowledge.TrustBoundary` checks the proofs and their transitive
axiom dependencies. The sampling program is also pinned as computable. This directory is
included in the default library build, and its trust boundary is imported by `CensusCheck`.
