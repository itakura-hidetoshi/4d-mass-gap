# PZ37ABS signed original-source error implementation plan

> Execute inline through GitHub MCP only. git/gh CLI is forbidden.

**Goal:** Quantify the signed error caused by the actual remote source weight S in ABR, without changing Wilson physics, dropping negative terms, or replacing either interacting GI posterior.

**Architecture:** A generic compact-integral relative-weight error lemma, followed by the actual source remote-weight comparison exp(24*b). Combine S comparison with ABQ2's R comparison to control V=S/R by exp(80*b), and apply the signed estimate to the original full kernel and ABR's true t*Omega corrected density formula.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User's 2026-10-31 ABQ2 handoff, ABR #6026 MERGED, and continuation instruction. Exact authoritative base bb6c8559693dd7bb48806408829b42c79828477a.

## Global constraints
- Same original Wilson model, actual four-edge embedding and actual remote complement, spatial half-weight, positive Perron representative and physical transfer norm.
- Add new leaf files only; no change to existing Lean declarations, pins, workflows or public roots.
- No sorry, admit, new axioms or native_decide.
- Use ABR's local Fin 2 Fintype, Link DecidableEq and measurable-space implementations.
- A relative error estimate is not an absolute uniform source mass or GI lower floor.
- Merge only after completed exact-source workflow/job/Lean step, zero changed-file diagnostics, standard axioms and completion receipt.

## Approaches and decision
Directly infer positive signed overlap from positive R: rejected (cancellation remains possible).
Normalize away the actual physical mass: rejected (changes the claim).
Chosen: retain an arbitrary actual anchor S(y) and derive the exact signed error, including the full |f| budget. This gives a conditional positivity margin, not an assertion that the genuine GI margin holds.

## Review focus
- All finite H, including H=0; b=0 allowed in comparisons.
- Negative/sign-changing f retained, integrability of every term established.
- Constant exp(24*b) arises from four actual links, not total lattice cardinality.
- V=S/R stays explicit in the corrected physical formula; t is never replaced by a temporal Haar power.
- No source or posterior surrogate is installed as the actual model.

## Tasks
- [ ] Generic two-sided relative comparison implies absolute difference budget.
- [ ] Compact weighted signed integral anchored error and lower bound.
- [ ] One-link spatial half-weight exp(6*b), four-link exp(24*b), actual remote S two-sided comparison.
- [ ] Actual correction V relative comparison exp(80*b).
- [ ] Original full-kernel signed error/lower bound, positivity conditional on an explicit margin, and identical corrected-Perron statement.
- [ ] Review both full new files and dependent signatures; run exact-source CI and read the whole diagnostics relevant to new modules.
- [ ] Synchronize mathematical documentation only for verified results, preserving historical records.

## Verification ledger
Local lean/lake unavailable. New-module static contract was run before implementation and failed on missing RealIntegralRelativeWeightSignedError.lean as expected. A static green result is not kernel verification. The existing GitHub Actions workflow is the proof gate. No subagent tool is available, so review is inline and not described as independent expert review.
