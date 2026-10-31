# P4-Q2-PZ37ACC Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans with parallel implementation and an independent whole-file mathematical review. All GitHub operations use MCP; git/gh CLI is forbidden.

**Goal:** Bound the unchanged full two-posterior GI response directly by the actual energy covariance and variance, and prove the genuine centered-source gauge obstruction to a fixed orientation of tail dominance over all outer contexts.

**Architecture:** Append one generic defect algebra leaf, one original-model covariance/GI leaf, and two centered-source gauge leaves. Derive the GI envelope from ABY's complete signed-tail sandwich and ABZ's exact part balance, using ACA's bound on the entire negative moment. Transport all physical symmetries through the true Perron representative and actual right-boundary coordinate replacement.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User's ABY handoff, verified ABZ/ACA completion and explicit continuation to ACB. Original development base f3cb167e576250dd55b630cec1d448cbadf90a6d. Concurrent ACB PR #6046 and docs PR #6048 have since merged. Final integration base is 9dde4d0174f85292f5b17eefcdef8e2cf2502701; preserve both new ACB leaves and all documentation. The present four-leaf development is therefore numbered PZ37ACC. The GI leaf imports the merged ACB transfer-defect certificate.

## Global Constraints

- Append-only / tighten-only / overwrite-forbidden / same-root; new leaves only.
- Sole theorem authority formal/real-hilbert-uniform-coercive-strong-limit. Main is documentation mirror.
- Preserve original Wilson model, Gauss-law source, physical Hilbert space, true Perron representative, transfer norm, both posterior laws and outer pair-Haar.
- Source centering is the original spatial Haar-L2 centering. Updated joint half-density remains in U.
- Auxiliary two-copy SU2 Haar and original outer configuration pair-Haar remain distinct.
- No sorry, admit, new axioms, unsafe/native_decide, linter suppression, assumed actual smallness or unproved volume uniformity.
- Exact-source workflow/job/Lean step and independent completion receipt must complete SUCCESS before squash; every public axiom report standard-three only, no sorryAx, changed warnings/errors0/0.
- Reobserve source/squash Git tree and immediate/final authoritative HEAD. Preserve old README/ROADMAP history.

## Approaches and Decisions

The user authorized continued formalization and verified merge with minimal procedural questions. We selected the complete covariance balance rather than only strengthening a local rectangle: it supplies a direct unconditional GI envelope and dominates the existing rectangle bound that uses the same optimized mismatch budget. A swap of the inner rectangle gives a valid two-region improvement, but is deferred because the direct full-balance estimate subsumes that route. The actual centered-source gauge symmetry supplies a model-specific obstruction, not an assumed small residual.

## Review Focus

- Numeric defect identities include b=0 and v=0 where stated. Without covariance Cauchy, v=0 does not force C=0.
- The ratio/defect equivalence requires b>0 and 0<=r<=1; keep the favorable covariance sign explicit.
- The GI envelope uses the exact positive-minus-negative balance. Never insert an upper bound for positive mass as though it were a lower bound.
- Gauge symmetry acts simultaneously on both original outer boundaries, with an actual central gauge at the chosen link source. The coordinate update is literal Function.update.
- Use the real Perron physical L2 eigenvector and its continuous representative to prove pointwise gauge invariance; no invented independent-boundary invariance.
- Tail-moment exchange does not claim GI sign exchange or invariance of the two fixed posterior anchors.
- The unconditional all-context obstruction concerns at least one ABX-active link for each H,b>0, not every link. Local-event tail control remains open.

## Tasks and Interfaces

- [ ] Add CompactEnergyMismatchDefect.lean: exact opposite-budget product, defect rationalization and strict threshold criteria; favorable-covariance sqrt-defect bound; exact budget-ratio iff favorable sign and relative regression defect. Public analytic mismatch bound uses genuine Var(E)=1/4.
- [ ] Add PhysicalYangMillsWilsonSU2OriginalCovarianceGIBoundsV5_PZ37ACC.lean: original full-GI two-sided covariance envelope, absolute error and absolute-response lower bound, same-Perron expression, strict positivity criterion through actual regression defect, domination of ACA's rectangle lower margin, and original outer pair-Haar second-moment consequence under an explicit event margin.
- [ ] Add PhysicalYangMillsWilsonSU2OriginalGaugeTransferSymmetryV5_PZ37ACC.lean: original centered source, true Perron/joint density gauge invariance, central gauge map and exact P/U/F transformation.
- [ ] Add PhysicalYangMillsWilsonSU2OriginalGaugeMismatchObstructionV5_PZ37ACC.lean: actual covariance/variance/defect and full cross-part exchange; actual active-link impossibility of all-context strict one-sided tail dominance.
- [ ] Independently review all new sources/imports/dependent signatures/pinned APIs; run the existing exact-source dependency-aware CI and fix diagnosed structural failures without weakening statements.
- [ ] After all gates, squash to authority and append README/ROADMAP on authority and main. For documentation-only commits, use GitHub's documented skip-ci message to avoid the observed unconditional legacy main-push builds; preserve any required check gate, and do not change workflows.

## Validation

Formal theorem statements and all public #print axioms are the meaningful verification surface. No local Lean runtime is available. Use the mandatory exact-source CI, completed full logs, independent receipt, and GitHub MCP tree/ref reobservation. Previous elaboration lessons: typed scalar integrals; explicit quarter-term identity; add_le_add_right fixes the summand on the left in the pinned API, so use explicit add_le_add where ordering matters.

## Concurrent-authority integration

While the initial source was in CI, another ACB theorem PR #6046 merged at 8721fe3bb5dc283ac55f67f27a254db18581973f, followed by docs-only #6048 at 9dde4d0174f85292f5b17eefcdef8e2cf2502701. Source/merge-test tree comparison detected the change. Preserve that entire base, rename only this PR's unmerged physical leaves and identifiers to ACC, and rerun exact-source CI on the combined tree. No merged source is renamed or overwritten. The next stage after this PR is ACD.
