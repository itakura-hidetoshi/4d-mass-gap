# PZ37K original diagonal fourth-Haar implementation plan

Goal: prove the original diagonal response is boundary-independent at every finite H, using its actual normalized SU(2) Haar integral.
Spec: the user's 2026-10-26 PZ37J handoff; base 7798efe8e12319551f48904992f1a18e3fe0e146.
Architecture: derive a character-square single-link projector from the existing quaternion orbit identity; apply at any unused physical plaquette edge. For a quadruple covering all four edges, use its established Nodup and the true centre flip to remove each single-occurrence energy. Sum the original fourth-crossing expansion and apply the original Haar boundary translation.
Tech stack: Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

Constraints: original Wilson action, normalized Haar, posterior and source unchanged; no new axiom, sorry, admit or native_decide. Keep H=0 and repeated crossing indices. Distinguish seventh jet from the actual minor remainder. Do not claim U0, rank3 or mass gap.

- [ ] Derive normalized character-square orbit and forward/inverse original spatial Haar projection. Check all four genuine edge orientations.
- [ ] Prove centre-even weights remove any list of distinct temporal energy factors, with all continuity/integrability obligations.
- [ ] Prove every original diagonal fourth term is boundary-independent by the covered/free-edge dichotomy, then sum to D_H.
- [ ] Derive zero diagonal wedge, all-period overlap-only jet, and unconditional H>=1 Vandermonde jet.
- [ ] Compile all changed sources, inspect all axiom reports and independent review, check exact-head CI and completion receipt before squash merge.

Review focus: normalized character gives 1/4; coinciding crossing indices; H=0 four edges remain distinct; inverse edge orientations; jet/minor distinction.

Execution: native implementation in a separate branch of a fresh clone. User supplied the research design and authorized continuing without procedural confirmation. Formal theorem statements and kernel checking replace behavior-unit tests.
