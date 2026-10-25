# PZ37F sixth Haar transport implementation plan

**Goal:** Transport the original interacting two-slab sixth stripped Haar moment to the PZ37D four-sector wedge and connect it to the physical PZ37B seventh jet coefficient.

**Architecture:** Keep the original Wilson actions and normalized spatial Haar. Expand the inner sixth binomial, retain its fifth affine correction and sixth marginal, prove the affine outer residual, then cancel that residual only inside the alternating boundary determinant. Apply PZ37C to the polynomial baseline and retain the configuration-dependent sixth obstruction separately.

**Tech stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User's 2026-10-26 PZ37F continuation instruction; authoritative starting commit 2e2687cb98773a3dc1e9900210d86a3cf033f58e on formal/real-hilbert-uniform-coercive-strong-limit.

## Constraints and review focus

- No new axioms, sorry, admit, or native_decide proof replacement.
- Retain the full intermediate spatial weight twice, the inner fifth correction, and all sixth sectors.
- Include every finite period, including H=0; no extra positivity or nondegeneracy premise.
- Do not identify the two-slab sixth moment with the auxiliary r=2 moment.
- Do not assume physical sixth observables factor through the scalar endpoint action.
- No obstruction vanishing, physical minor eighth-order remainder, nonzero rank-three, or mass-gap claim.

## Tasks

- [ ] In OriginalTwoSlabSixthTransportV5_PZ37F.lean, prove parameter-integral continuity, the complete inner/outer sixth expansion, the affine boundary residual (45/8)*m1*(wB-wA), and the wedge equality with the four PZ37D sectors.
- [ ] In OriginalSeventhPhysicalVandermondeV5_PZ37F.lean, prove the genuine endpoint moment bridges through sixth order and the physical identity C7 = -V/512 - [w,Phi6]/720 using PZ37B/C.
- [ ] Verify both complete modules, inspect every added theorem's printed axioms, and independently review physical definitions, signs, H=0, and missing assumptions.
- [ ] Publish the source through GitHub MCP, verify the exact PR HEAD CI and completion receipt, squash merge only when GREEN, and confirm authoritative HEAD equals the squash SHA.

## Execution notes

The user has explicitly authorized the proof route, necessary GitHub writes, and GREEN-gated squash merge. Kernel checking of the full theorem statements is the primary mathematical test; separate tests that mirror proofs are not added. Changes stay in isolated feature branch formal/p4-q2-pz37f-original-sixth-vandermonde-transport.
