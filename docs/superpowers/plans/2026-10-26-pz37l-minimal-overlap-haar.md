# PZ37L Minimal-overlap Haar Implementation Plan

> For agentic workers: use superpowers:executing-plans; implement natively and obtain one independent whole-branch review.

Goal: evaluate the genuine period-two exceptional pair response without assuming constancy, vanishing, or nonvanishing.
Architecture: select exactly the four odd-incidence insertions and their 24 permutations; contract the two shared Haar coordinates by genuine character-pair and conjugation projectors, then contract the four remaining Wilson energies. Connect the actual 48 ordered spatial pairs to the two orientations of the six-link calculation.
Tech Stack: Lean v4.30.0-rc2, mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Spec: the user's PZ37J handoff and continuation after PZ37K, base 6fc795c03995c9cd1d5b7274b14b5516728b96b6.

Global constraints: preserve original SU(2) Wilson action, normalized Haar, Gauss-law source, posterior-fiber, and the twice-counted middle spatial action. No new axiom, sorry, admit, native_decide. Only formal/real-hilbert-uniform-coercive-strong-limit is authoritative. Seventh Taylor jet remains distinct from the actual minor and its O(|beta|^8) remainder.

Review focus: normalized character Tr/2 and its 1/4 contraction; shared-edge orientations; all repeated crossing indices; both orientations of actual period-two overlap; no unsupported nonzero/constant inference.

- [x] Implement weighted character-pair and conjugation projectors in the original full spatial Haar; derive the six-link response with coefficient 1/1024.
- [x] Implement exact 24-fold odd-edge support reduction and the actual period-two geometry, connecting all 48 pairs to the six-link response.
- [x] Implement the sum of the boundary loop products and transport the formula to the physical seventh jet; record any remaining obstruction accurately.
Completion gate, recorded in PR #5915: changed-source dependency closure, all new theorem axiom reports, independent review, exact-head CI and receipt must pass before GREEN squash.

Formal theorem statements and Lean kernel checks are the tests. User-authorized native execution and GREEN squash continue without a procedural approval pause. GitHub MCP performs remote writes. Existing dependencies are not refactored.

Implementation record: all four source files written. Independent whole-source review found no issues; reviewer leaves compilation/transitive axioms and CI to the kernel checks. First CI exposed an inferred composition/measure mismatch in integral_finset_sum; an explicit Integrable fact fixes it. Second CI verified the shared-link projectors and two-shared-edge theorem, then exposed one unreduced lambda in the two-cycle rewrite; beta reduction is now explicit. The abstract 24-fold permutation lemma and six-link odd-support logic were checked separately against the pinned mathlib. Final exact-head status is recorded in the PR.
