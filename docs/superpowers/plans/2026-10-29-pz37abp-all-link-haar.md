# P4-Q2-PZ37ABP implementation plan

> Execution: one independent generic-measure implementer, main-agent physical integration, and a fresh whole-change reviewer. GitHub MCP is the sole repository mutation path.

**Goal:** Prove the exact restriction of the original all-link temporal Wilson convolution to the four actual links of every physical plaquette.

**Architecture:** Split the finite coordinate set into the embedding range and its complement, transport the genuine product Haar by measurable equivalences, apply finite-product Fubini, and reindex the selected block. Normalize each actual temporal factor by its proved positive one-link Haar mass; the complementary integrals are exactly one. Rewrite the resulting identity back to the original all-link kernel and its full power of the mass.

**Tech stack:** Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

**Spec:** User's 2026-10-29 ABP handoff; sole theorem source `formal/real-hilbert-uniform-coercive-strong-limit` at `3b168eb70e594c3719f3dac7f5fc9d6a76ae5600`.

## Global constraints

- Append only; preserve all original kernels, spatial interactions, Perron vacuum, two interacting posteriors, pair Haar, physical transfer norm, previous proofs and no-go results.
- Use the actual MY four-edge embedding, including the smallest lattice `H=0`.
- No new axiom, admitted proof, weakened hypothesis, changed pin, or replacement posterior.
- Distinguish all-link temporal convolution on reference Haar from the full physical transfer.
- Merge only after completed exact-source CI, changed-Lean error/warning 0/0, standard-axiom reports without `sorryAx`, independent completion receipt and independent review.

## Tasks and interfaces

- [ ] Generic leaf `FiniteProductWeightedEmbeddingIntegral.lean`: prove unnormalized finite weighted embedding factorization and the coordinate-mass-one specialization. Inputs: sigma-finite homogeneous coordinate measure, finite index embedding, real weights and real selected test. Outputs: exact original integral equals selected integral times complementary one-coordinate masses.
- [ ] Physical leaf `PhysicalYangMillsWilsonSU2OriginalAllLinkTemporalHaarRestrictionV5_PZ37ABP.lean`: identify the original list-product crossing kernel with the finite coordinate product; prove full and complementary mass, normalized restriction, and ordinary integrability for continuous selected tests.
- [ ] In the physical leaf, transfer the existing ABO3 character/centered-half-energy identities and variance floor to integrals of the unchanged all-link temporal kernel.
- [ ] Review complete new files, imports and pinned APIs; run dependency-aware changed-Lean CI; inspect completed Lean output, all public axiom reports, test checkout/source tree agreement and independent receipt; then squash merge.

## Review focus

- Every actual link occurs once; both forward and inverse plaquette orientations remain those of ABO/MY.
- Complement coordinates retain the same target configuration and contribute their actual masses.
- The full denominator is `Z_b ^ card Link`, while the selected denominator is `Z_b ^ 4`; neither is the physical norm `t`.
- No positivity assumption on coupling is required for identities; the positive interval is required only for the existing lower floor.
- Generic total-integral identities also allow arbitrary real tests; continuous physical tests have a separate genuine integrability statement.

## Validation decisions

The local environment has no Lean/Lake executable. The mathematical theorem statements are the verification contracts; compilation and axiom evidence will come from the existing pinned GitHub Actions checker. No deliberately invalid proof or redundant implementation-mirroring test is added. Isolation is a new GitHub branch from the observed exact source, with no git/gh CLI operations.
