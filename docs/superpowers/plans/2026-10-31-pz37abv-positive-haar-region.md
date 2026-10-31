# P4-Q2-PZ37ABV Positive Haar Region Implementation Plan

> For agentic workers: execute the already-authorized continuation with independent geometry and API review; preserve the exact physical definitions and verify all new proofs with the pinned Lean kernel.

**Goal:** Upgrade ABU's single-pair determinant floor to an explicit positive-Haar-mass region and a volume-independent lower bound on the actual restricted determinant integral.

**Architecture:** Use the existing genuine SU(2) quaternion orbit identity to cover the group by eight Haar translates of an energy cap. Connect these caps to the unchanged ABU temporal crossing and two original interacting posterior rows.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6; GitHub MCP and the existing dependency-aware CI.

**Spec:** User's 2026-10-31 ABU-to-ABV handoff, starting from authoritative `39b481be7bc2e64e406c66414f0a4224048727ef` and merged PR #6029.

## Global constraints

- Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. `main` is a documentation mirror.
- Append-only, tighten-only, same-root; no changed original hypotheses, Wilson model, Perron representative, normalization, posterior laws, pins, public imports, or workflows.
- GitHub MCP for repository operations; no git or gh CLI.
- This phase concerns the actual posterior determinant. Physical response alignment, negative-tail cancellation, full outer pair-Haar GI/source floors, all-Hilbert coercivity, continuum OS/Wightman and mass gap remain separate open obligations.

## Design choice

Continuity alone yields a neighborhood with a positive but uncomputed Haar mass. Instead use the existing four quaternion square identity: at least one of four real character coordinates has absolute value at least 1/2. The two signs give eight actual Haar translates covering SU(2), so each energy cap has mass at least 1/8. This gives a fully numerical pair-mass bound without an added density formula or assumption.

## Task 1: Genuine SU(2) caps

Create `MGAP4D/MathlibAnalytic/SpecialUnitaryTwoWilsonEnergyHaarCapsV5_PZ37ABV.lean`.

- [ ] Verify fixed APIs and full imported quaternion/energy proofs.
- [ ] Prove the actual pi rotation acts by the central antipode, with `E(rot^-1*g)=2-E(g)`.
- [ ] Define low cap `E<=1/2`, high cap `3/2<=E`, and their product.
- [ ] Prove measurability, eight-translate coverage, equal antipodal cap masses, single-cap real mass at least 1/8 and pair-cap real mass at least 1/64.

## Task 2: Original interacting posterior restricted integral

Create `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveHaarRegionV5_PZ37ABV.lean`.

- [ ] Prove `cross_b(g,h)=2*b*(E(h)-E(g))`, continuity and the exact variation from `(1,rot)`.
- [ ] On the fixed pair cap prove `cross>=2*b` and `D>=2*b*exp(-32*b)` for `b>=0`.
- [ ] Prove continuity and integrability of the actual determinant using the existing ABT density continuity.
- [ ] Apply the genuine product-Haar restricted-integral inequality to prove `integral_cap D >= b*exp(-32*b)/32`, strictly positive for `b>0`, for every finite H, actual link and right environment.

## Review focus and verification

- Zero coupling is allowed in non-strict bounds; strict positivity explicitly needs `b>0`.
- Closed cap boundaries are included; eight translates cover every SU(2) element, not only a full-measure subset.
- Haar is the original normalized compact Haar; the two-copy law is the existing ABT auxiliary reference, not the outer physical boundary pair law.
- All `H`, link and right-background dependence stays in the unchanged density; region and constants have no such dependence.
- Read every changed Lean file, imported signatures and pinned API; print axioms for every exported theorem. Do not equate numerical sanity checks or static checks with kernel verification.
- Run existing exact-source CI; require workflow, job and Lean step all completed, changed-file warning/error 0/0, only standard three axioms, no sorryAx, and independent completion receipt.
- Independently review the complete additive change; squash merge only when all gates pass, then re-read the authoritative HEAD and merged SHA.

## Task 3: Documentation

- [ ] Add current ABR, ABS, ABT, ABU and verified ABV status to authoritative README/ROADMAP, retaining historical content and explicitly preserving the open obligations.
- [ ] Mirror documentation to main with a clear non-theorem-authority notice. Keep docs-only changes outside Lean-triggering paths.

No local Lean/Lake binary is present in this session. The existing GitHub exact-source kernel workflow is the proof-verification authority.
