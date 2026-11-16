# P4-Q2-PZ37AMH — authentic SU(2) Wilson Gibbs plaquette covariance from physical periodic time-coordinate separation

Date: 2026-11-16 JST.

## Certified theorem and exact parent

- Original AMF and AMG theorem/record/mirror are merged and untouched: AMG theorem [PR #6788](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6788) provides the original fixed-beta0 actual interacting SU2 Wilson Gibbs plaquette connected covariance bound at typed support separation.
- AMH theorem [PR #6791](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6791) **MERGED** into authoritative Formal with merge SHA `851a1f3f5da209bd5c8238af00cd533dd472be6b`, parents Formal `b77b4f4086451d1f8af789b5c60876f71f76dc95` and certified source `7db514b877bf57635a8bcb0d38d9727823c53b52`.
- Changed Lean file (additive only): `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0PlaquettePhysicalTimeSeparationV5_PZ37AMH.lean` (177 lines, 6 new theorems, 6 axiom prints).
- Unchanged: original four-dimensional SU2 Wilson action, compact Haar Gibbs measure, Gauss-law, AJA, fixed beta0 `log(3/2)/64`, prior AMF/AMG theorems, canonical root, Lean pin `v4.30.0-rc2` and mathlib pin `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## Precise physical theorem

Write `d_t(p,q)` for the shorter periodic cyclic distance between the **source-time base residues** of two actual four-edge periodic plaquettes `p,q` on the even side-length lattice `2(H+1)`, `H>0`. This is a physical **one-coordinate time distance**, not Euclidean 4D distance and not a random-scan Markov time.

For each physical boundary link `e` of `p`, its source-time cyclic distance from `p`'s base time is at most one. Hence for any actual boundary links `e∈∂p` and `f∈∂q`:

```text
d_t(p,q) <= 2 + d_t(e,f)
D + 2 <= d_t(q,p)
    ==> periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D (∂q) (∂p).
```

By the pre-existing physical Gibbs covariance theorem AMG, now with a **constructed** rather than assumed separation witness, the full interacting finite-volume original SU2 Wilson Gibbs fundamental-character covariance satisfies

```text
beta0 = log(3/2)/64
rho0 = 18 * (exp(4*beta0)-1)/(exp(4*beta0)+1)
0 <= rho0 < 1

if D+2 <= d_t(q,p):
  |Cov_(mu[H,beta0])(chi_p,chi_q)| <= 64 * rho0^D/(1-rho0)

unconditionally for any two plaquettes p,q, H>0:
  |Cov_(mu[H,beta0])(chi_p,chi_q)|
    <= 64 * rho0^(d_t(q,p)-2)/(1-rho0)
```

The natural-number exponent `d_t-2` is **truncated natural subtraction**, and is zero for neighbors/overlapping supports. No false positive physical separation for shared-link adjacent plaquettes is asserted.

## Six exact Lean theorem declarations

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, all with prefix `p4Q2PZ37AMH_`:

1. `originalBoundaryLink_baseTimeCyclicDistance_le_one`
2. `originalPlaquetteBaseTimeDistance_le_two_add_linkDistance`
3. `originalPhysicalPlaquetteSupports_separated_of_baseTime`
4. `originalFixedBeta0GibbsCovariance_abs_le_of_baseTime`
5. `originalPhysicalPlaquetteSupports_separated_by_baseTimeSubTwo`
6. `originalFixedBeta0GibbsCovariance_abs_le_baseTimeSubTwo`

## Independent exact-source proof verification

- [PR exact-source CI #43797665387](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43797665387), event=pull_request exact SHA `7db514b877bf57635a8bcb0d38d9727823c53b52`, attempt 1, workflow **completed/SUCCESS**.
- Main Lean job `133070065898` and required `Run changed Lean fast check` step **completed/SUCCESS**, actual pinned dependency build **11,511/11,511**.
- Six `#print axioms` audit receipts, each **only** `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; AMH changed-file warning/error **0/0**.
- Independent exact-HEAD receipt job `133072184774` **completed/SUCCESS**; exact receipt `event=pull_request exact_sha=7db514b877bf57635a8bcb0d38d9727823c53b52 source_result=success run=43797665387 attempt=1`.
- Source commit, GitHub test-merge commit `3d15cd63e2d7387b33bf10e9422ab9ee2785bd3e` and actual canonical two-parent theorem merge `851a1f3f5da209bd5c8238af00cd533dd472be6b` all carry Git tree `30005de0f63818558f6e86fa49b81e7392ee8d69`. Verified by direct GitHub Git-object reads.
- **Canonical postmerge push:** [CI #43798561047](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43798561047) was observed `in_progress` before record authoring. Do not promote this observation to completed or claim a canonical push receipt until the exact run, job, step and independent receipt are separately observed. Append its final outcome, without rewriting this historical observation.

## Open obstructions — no illegal promotion

1. This is an authentic **one time-coordinate projection** only. Full four-dimensional periodic Euclidean/L1 support geometry and polynomial 4D distance-shell cardinality are separate unproved bridges.
2. Existing `PeriodicHypercubicPlaquetteDistanceShellBound` has only a generic `24^D` upper bound. At beta0, rho0≈0.22806 and 24*rho0≈5.47349>1; this coarse shell bound cannot prove a uniform total correlation summability theorem.
3. Alternative possible route: genuine Dobrushin Green influence kernel row/column summability + finite link-to-plaquette incidence (at most six) + Gibbs covariance Green comparison. Each interface must be checked on the **same actual compact SU2 Gibbs system**. This is an unverified research plan, not a new AMH theorem.
4. The original H=0 (side length two), adjacent shared-link positive separation, Gauss-law OS physical one-slab transfer Hilbert identification, all-H physical transfer/Hamiltonian gap and continuum 4D Yang–Mills mass gap remain **OPEN/NO_DATA**.
5. The separate KuuOS CodeAI/standalone Lean MCP execution receipt is **NO_DATA**. Proof authority here is the exact GitHub Actions machine run, not an asserted CodeAI action.


## Postmerge canonical independent push receipt — observed after the pending entry

**Certified:** The actual Formal merge commit `851a1f3f5da209bd5c8238af00cd533dd472be6b` passed [independent event=push CI #43798561047](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43798561047), workflow **completed/SUCCESS**. Main Lean job `133072968316`, required `Run changed Lean fast check` step **completed/SUCCESS**, pinned dependency build **11,511/11,511** with newly built AMH leaf. All six AMH `#print axioms` again reported only `propext`, `Classical.choice`, `Quot.sound`, with no sorryAx and **0 direct AMH warnings/errors**. The distinct independent receipt job `133075116685` **completed/SUCCESS** and issued:

```text
[mcp-receipt] event=push exact_sha=851a1f3f5da209bd5c8238af00cd533dd472be6b source_result=success run=43798561047 attempt=1
```

The source `7db514b...`, GitHub PR test-merge `3d15cd6...` and canonical merged commit `851a1f3...` share identical Git tree `30005de0f63818558f6e86fa49b81e7392ee8d69`. This later observation **resolves the earlier pending canonical push status** without altering the historical entry.
