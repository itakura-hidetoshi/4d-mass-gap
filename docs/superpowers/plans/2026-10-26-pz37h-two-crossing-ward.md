# PZ37H Original Two-Crossing Ward Implementation Plan

**Goal:** Prove boundary invariance of F(i,2) for every original spatial Wilson power i, including F(4,2), and reduce the PZ37G seventh jet to F(2,4) alone.

**Architecture:** Preserve the exact original Wilson action and normalized spatial SU(2) Haar. A centre cut flips all links with one specified direction and one source coordinate. Opposite edges of each original plaquette receive the same central factors, so the spatial action is unchanged. Two different temporal trace links are separated either by this cut or, when their cut keys agree, by a centre gauge transformation at one source vertex. Diagonal temporal insertions use the full vertex-gauge change of variables. Integrate the actual finite double-link expansion of Cross squared.

**Tech stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User continuation of PZ37G, authoritative starting HEAD 1571c1ee703b1991f4542c74d76d90804670c300; formal/real-hilbert-uniform-coercive-strong-limit is the sole theorem carrier. The user authorized direct GitHub MCP writes and squash merge after exact-head GREEN plus completion receipt.

## Constraints and review focus

No new axioms, sorry, admit, native_decide, alternate physical model, altered Haar, or omitted intermediate plaquettes. Include H=0 and i=0. Never infer full sixth-obstruction vanishing from the removal of F(4,2). F(2,4), the physical eighth-order remainder, rank three, volume-uniform coercivity and continuum gap remain separate.

## Tasks

- [ ] OriginalCutCenterHaarV5_PZ37H.lean: original cut geometry, central four-edge cancellation, Haar preservation, single and distinct-pair weighted temporal trace zero.
- [ ] OriginalAllPowerTwoCrossingWardV5_PZ37H.lean: genuine single-link power gauge Ward, distinct-link energy pairing, finite double-link expansion, F(i,2) invariance, physical seventh jet with one surviving F(2,4) wedge.
- [ ] Kernel-check every complete theorem statement and proof; inspect all new theorem axiom reports and changed-file warning/error 0/0. The Lean theorem goals are the mathematical tests; no unproved placeholders are committed.
- [ ] Review original definitions, periodic wraparound, inverse orientations and coefficient signs; verify same-head CI and receipt; squash merge only on success and check authoritative HEAD against merge SHA.

## Design decisions

Direct symmetry is preferred to a fourth-plaquette combinatorial expansion because it proves all spatial powers at once. A vertex-only argument would miss reciprocal links at minimal period, so the cut transformation is indispensable. The positive-direction cut key is (direction, source coordinate in that direction); equal keys and distinct links have different source vertices, and one source cannot be the other target since the genuine period has a nontrivial unit shift. Work is isolated on formal/p4-q2-pz37h-original-two-crossing-all-powers.
