# PZ37ABT genuine two-posterior signed pairing implementation plan

> Execute inline. Repository operations exclusively through GitHub MCP; no git/gh CLI. New isolated branch based on the exact authoritative commit.

**Goal:** Express the unchanged genuine GI signed expectation gap as an exact symmetric two-copy pairing of the two genuine normalized posterior densities, retaining its full positive and negative contributions.

**Architecture:** First prove a generic compact-space two-density identity and the exact exponential cross-determinant factorization/sign criterion. Then specialize to the existing GI receiver and its original identity/pi-rotation interacting posterior rows. The product reference uses two auxiliary copies of the one-link Haar space; it is not an independence assertion about original lattice links and is not the outer physical boundary pair-Haar.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** 2026-10-31 user continuation after merged ABS #6027. Authoritative branch formal/real-hilbert-uniform-coercive-strong-limit, exact base 59814cd69781b6ebae9bcf605e79441dad4b88bf. Original GI definition and Haar-pairing theorem at that commit are the physical authority.

## Global constraints
- Add new leaf files; do not change existing Wilson definitions, Perron representative, transfer norm, theorem hypotheses, pins, public roots, workflows.
- No sorry, admit, new axiom, native_decide, or skipped dependency verification.
- Keep both original normalized posterior laws. Do not replace either by unweighted Haar.
- No uniform positive GI margin is inferred from positive densities alone.
- Separate exact identities from conditional tail criteria and unresolved physical positivity.
- Merge only after completed exact-source workflow/job/Lean step, changed-file warning/error 0/0, standard axioms, and separate completion receipt.

## Approaches
Repeating ABS's coarse absolute error budget is rejected: it cannot certify a positive Haar-centered temporal margin. Replacing the posterior with Haar is rejected: it changes the model. Selected approach: exact antisymmetrized cross-density determinant with a common positive exponential factor; retain signed differences before integration.

## Tasks
- [ ] Generic cross-density product integral identity; symmetric signed pair; normalized exponential mass one; cross-determinant positive factor and sign equivalence.
- [ ] Generic continuous positive-minus-negative integral decomposition.
- [ ] Specialize the original GI receiver and both exact posterior densities; prove exact pair formula, continuity, integrability, signed decomposition, explicit conditional margin bound, and exact log-odds determinant sign criterion.
- [ ] Static contract and finite rational identity sanity checks; kernel checks exclusively through exact-source CI because local Lean/lake are absent.
- [ ] Review all new Lean text and pinned APIs; repair actual failures, never mask them; update PR evidence.

## Verification ledger
Static contract was run before the new files existed and failed on missing CompactTwoDensitySignedPairing.lean; after implementation it passes for all 17 exported theorem names and axiom-print commands, with no forbidden proof tokens. The GitHub blob SHAs exactly match the locally reviewed source bytes. 175 finite rational identity/sign-decomposition checks pass. These checks are not Lean theorem validation. No local Lean/lake executable is installed; CI is the decisive proof gate. No reviewer/subagent tool is available, so no independent expert review is claimed.
