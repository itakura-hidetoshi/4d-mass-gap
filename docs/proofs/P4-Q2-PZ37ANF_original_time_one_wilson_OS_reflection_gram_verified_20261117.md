# P4-Q2-PZ37ANF — actual original Wilson time-one OS reflection form and Gram-moment square

Date: 2026-11-17 JST. Authoritative root: \`itakura-hidetoshi/4d-mass-gap\`. Canonical theorem branch: \`formal/real-hilbert-uniform-coercive-strong-limit\`. Pinned Lean \`v4.30.0-rc2\`, mathlib \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`. Protocol: append-only, tighten-only, overwrite-forbidden, same-root, exact-source CI and independent integrated-HEAD push; docs-only **no** Strict Lean rerun.

## The certified mathematical result (finite volume, exact source)

Use the original SU(2) even-periodic four-dimensional Wilson Gibbs probability, coupling \`beta >= 0\` and lattice parameter \`H : ℕ\`. The positive-time carrier is the ACTUAL shared reflection-fixed boundary times the positive open-half configuration. The observable is **literally** the same time-one two-Wilson-mode cylinder of ANC/AND/ANE via the certified coordinate equivalence; no substitution of ANA's separately normalized temporal-gauge half-path law occurs.

Define the original real Wilson OS quadratic form by integrating the actual full-configuration reflected product:

\`Q_OS(H,beta,c0,c1) = ∫ A, F_{c0,c1}(boundary(A), positive(A)) · F_{c0,c1}(boundary(θ A), positive(θ A)) dμ_W(A)\`.

Use the ALREADY PROVED original Wilson boundary-fibered Gibbs factorization and Gram feature \`G_{H,beta}(b,x)\`. ANF establishes the actual exact identity

\`Q_OS(H,beta,c0,c1) = ∫ b, | ∫ x, G_{H,beta}(b,x) F_{c0,c1}(b,x) dλ_open(x) |² dλ_boundary(b)\`.

This entails unconditional \`Q_OS >= 0\` for **every** real coefficient pair. It makes the missing **strict** positivity problem explicit: a strictly positive boundary-Gram-moment squared integral is sufficient for \`Q_OS > 0\`. The required strict boundary-moment integral has **not** been proved here and is not silently assumed for any ANE nonzero L² class.

## Exactly audited original Lean file

One additive Lean file, 228 lines:
\`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicTimeOneOSReflectionFormV5_PZ37ANF.lean\`.

Five theorem declarations:
1. \`p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable\`.
2. \`p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le\`.
3. \`p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_nonneg\`.
4. \`p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq\`.
5. \`p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_pos_of_boundaryMoment\` — CONDITIONAL on a strictly positive boundary integral, not an unconditional strictness theorem.

All five complete \`#print axioms\` outputs depend ONLY on \`propext\`, \`Classical.choice\` and \`Quot.sound\`. No \`sorryAx\`; no warning/error in new file. This is genuine original full-periodic Gibbs OS reflection form, not an abstract Gram toy replacement.

## Exact-source GitHub CI

- Formal base for ANF: \`c3b1c35d7f618d17905e8dbb1b55287250241b23\`.
- [Theorem PR #6862](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6862): MERGED.
- Original AND/ANE/ANC source modules, bounded-measurable original Wilson reflection theorem and boundary Gram fiberwise square identities were read and reused. No old theorem/hypothesis weakened.
- Exact certified candidate HEAD: \`29ea9cfdf71bd8929e7c832682c5ee09e55b1f3f\`.
- [Exact-source pull_request workflow #44077115100](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44077115100), attempt 1: completed/SUCCESS. Required changed-Lean job \`134017879930\` and \`Run changed Lean fast check\` step completed/SUCCESS.
- Actual Lean log: \`Build completed successfully (8864 jobs)\`; 5/5 theorem audits standard 3 axioms only; \`sorryAx\` none; changed warning/error 0/0.
- Independent exact-source receipt job \`134019395907\`: completed/SUCCESS:

\`\`\`text
[mcp-receipt] event=pull_request exact_sha=29ea9cfdf71bd8929e7c832682c5ee09e55b1f3f source_result=success run=44077115100 attempt=1
\`\`\`

## Test-merge / actual Formal identity and independent push

- Source Git tree = \`4616bc62658453160dc014b0b0c48cd4cb850188\`.
- PR test-merge commit = \`0b1ece2fad44ecfa0ef80d2f2243125f7d53fa7f\` with parents (original Formal base, exact source); test-merge Git tree = \`4616bc62658453160dc014b0b0c48cd4cb850188\`, exact match.
- Squash merged theorem Formal HEAD = \`79ebe826acd2185862560bcda4c88b4a4f08fe45\`; actual integrated Git tree = \`4616bc62658453160dc014b0b0c48cd4cb850188\`, exact match with certified source and test-merge.
- Independent [Formal push CI #44077693517](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44077693517), attempt 1, event=push, actual integrated HEAD: completed/SUCCESS. Changed Lean job \`134019857939\` and required Lean build step completed/SUCCESS. \`Build completed successfully (8864 jobs)\`, five audits standard-three, zero \`sorryAx\`, ANF file warning/error 0/0. Exact-head receipt job \`134021689121\` completed/SUCCESS:

\`\`\`text
[mcp-receipt] event=push exact_sha=79ebe826acd2185862560bcda4c88b4a4f08fe45 source_result=success run=44077693517 attempt=1
\`\`\`

Current status: \`FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED\` — only the specific five finite-volume ANF statements, not any wider inferred assertion.

## Explicit unsolved obstruction / next stage

ANE proved nonzero ordinary Gibbs/Haar L² classes; ANF proved their actual original Wilson **nonnegative** OS reflection form and exactly identified the boundary-conditioned Gram moment square.

**No proof yet** that this specific physical top-eigenspace-orthogonal time-one two-mode cylinder has a nonzero boundary Gram moment (and hence \`Q_OS>0\`). The canonical OS-null space can be nontrivial; mutual absolute continuity of probability measures does not remove an OS-null vector. In particular the existing zero-coupling boundary-moment degeneracy theorem shows the Gram feature loses boundary dependence at \`beta=0\`; a proposed uniform strictness theorem for all \`beta>=0\` requires separate scrutiny and must not be assumed.

Not certified: positive OS seminorm of this witness, physical OS Hilbert quotient injection/identification, exact original Wilson one-slab ↔ completed OS intertwinement, volume-uniform transfer gap, continuum four-dimensional Yang–Mills construction and mass gap.

No CodeAI local execution or separate Lean MCP successful run is claimed: the actual mechanical certification was GitHub Actions' pinned Lean build with independent source and push receipts. This document is a historical proof record, not proof authority by itself.
