# P4-Q2-PZ37AMA — exact original-Wilson scaled relative-cost obstruction

Date: 2026-11-16 JST. **Theorem PR [#6771](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6771) MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit` at canonical merge commit `fbb609791eb0ad93e78b5c266eb34d39b24737da`.

## Original physical model and mathematical scope

One NEW append-only Lean file:

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0OptimalScaledRelativeCostV5_PZ37AMA.lean`

All 10 new declarations carry individual `#print axioms` commands. The original finite-volume SU(2) Wilson action, true product Haar measure, Gauss-law physical Hilbert carriers, original AJA condition, normalized transfer operators, actual `beta0=log(3/2)/64`, import roots, pinned Lean and mathlib remain unchanged.

Set `p_H=||P_H||>0`, `a_H=||A_H||`, `r_H=||R_H||`. ALX proves the exact original **same-volume** identity `a_H=p_H*r_H`. For *any* admissible ALY scalar comparison with common `s_H`, `eta_H>=0`, `xi_H>=0`, strictly positive `d_H=s_H*p_H-xi_H`, and

```text
a_(H+1) <= s_H*a_H + eta_H,
d_H <= p_(H+1),
t_H = (eta_H + xi_H)/d_H,
```

AMA proves **without assuming a new cross-volume physical map**

```text
max(r_(H+1)-r_H, 0) <= t_H.
```

The lower bound is *algebraically sharp*: `s_H=p_(H+1)/p_H`, `xi_H=0`, `eta_H=p_(H+1)*max(r_(H+1)-r_H,0)` yields `t_H=max(r_(H+1)-r_H,0)`. **This eta depends on the UNKNOWN next-volume excited norm**, hence is *not* an independently proved Wilson finite-size estimate. Free choice of common scalar scale cannot manufacture small, summable errors.

For all finite H the true positive variation `V_H=sum_{i<H}max(r_(i+1)-r_i,0)` is a necessary lower bound on *every* admissible ALY total cost. If `V_H>=1-r_0`, the ALZ **strict sufficient** cost budget `sum t_i<=T<1-r_0` fails for that H. Neither this obstruction nor failure of an ALZ criterion implies the mass gap is absent. The ALZ positive-variation sufficient condition is *not* necessary for an all-H gap.

## Actual 10 declarations audited

All in `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, prefix `p4Q2PZ37AMA_`:

1. `generic_fullNormCanonicalScale`
2. `generic_positiveIncreaseStep`
3. `generic_canonicalScaledCostWitness`
4. `generic_anyScaledCost_ge_positiveIncrease`
5. `originalFixedSharpPositiveNormIncrease`
6. `originalFixedSharpPositiveNormIncrease_nonneg`
7. `originalFixedSharpIncrease_le_anyScaledCost`
8. `originalFixedCanonicalScaledCost_eq_sharpIncrease`
9. `originalFixedSharpVariation_le_anyScaledCostSum`
10. `noSmallLinearCostBudget_of_sharpVariation`

## Exact machine and merge evidence

- Exact source HEAD `f1c2bf588714d50cba079368a446d14e48955d82`, new Lean blob `ac5a6365464394992a9ef0b9031b0c339e2d15b0`.
- PR [Exact-source CI #43759790656](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43759790656): workflow and Lean job **completed/SUCCESS**; pinned Lean **11,491/11,491**; AMA 10/10 actual axiom outputs only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, no AMA changed-file warnings/errors. Independent receipt job `132953255277` **SUCCESS**:
  `[mcp-receipt] event=pull_request exact_sha=f1c2bf588714d50cba079368a446d14e48955d82 source_result=success run=43759790656 attempt=1`.
- The initial `div_eq_iff₀` API was unavailable under pinned mathlib; replacement using `field_simp` succeeded but an unnecessary `ring` caused two Lean linter warnings. Final proof removed the redundant `ring` without changing theorem statements and passed the above exact-source CI. Do not retrofit success to these earlier failed/warning sources.
- Exact source tree, GitHub synthetic test-merge tree, and **canonical actual merge** tree all equal `97239e84f3760795ada2a504119806ded20cc9f2`. Merge commit `fbb609791eb0ad93e78b5c266eb34d39b24737da` has parents `54a50f7edb5254bb3db7478c4ec1c0b7f31ac7b1` and `f1c2bf588714d50cba079368a446d14e48955d82`.
- Independent *postmerge* [push CI #43760759944](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43760759944) was observed **in_progress** at first reading; it is not certified by the prior PR-source CI. A later completed result, if independently observed, is appended below without rewriting this observation.
- Fixed Lean `v4.30.0-rc2`; pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- CodeAI/Lean-MCP execution receipt: **NO_DATA** in this GitHub-MCP-only sequence; do not imply it ran.

## Physical next task and obstruction (OPEN / NO_DATA)

Independent physical original SU(2) Wilson plaquette/character cluster coefficients; Gauss-law/Haar-compatible typed neighboring-volume embeddings; quantitative raw and full two-volume comparison; summably small relative cost, or an independent direct spectral criterion, are unproved. The certified original Haar character moments `E[chi]=0`, `E[chi^2]=1/4`, `|chi|<=1` are legitimate starting data, **not** already a cluster bound. Original beta0 uniform all-finite-volume transfer gap, Hamiltonian mass gap and continuum four-dimensional Yang–Mills mass gap remain **OPEN/NO_DATA**.

## Independent authoritative postmerge CI certification — 2026-11-16 JST

The separately triggered [event=push workflow #43760759944](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43760759944) on **canonical formal HEAD `fbb609791eb0ad93e78b5c266eb34d39b24737da`** completed **SUCCESS**. Changed Lean job `132954813399` and independent completion receipt job `132956229058` both completed/SUCCESS; the actual `Run changed Lean fast check` step completed/SUCCESS.

The full pinned dependency closure built **11,491/11,491**; new AMA 10/10 full-qualified `#print axioms` outputs showed only `propext`, `Classical.choice`, `Quot.sound`. No AMA `sorryAx` or changed-file warnings/errors. The independently published observed receipt is:

```text
[mcp-receipt] event=push exact_sha=fbb609791eb0ad93e78b5c266eb34d39b24737da source_result=success run=43760759944 attempt=1
```

This verifies the *actual merged* unchanged tree `97239e84f3760795ada2a504119806ded20cc9f2`; prior PR-source CI was not reused as postmerge evidence. The certification covers the exact stated conditional Lean mathematics, **not** an independent original-Wilson cross-volume physical estimate or continuum Yang–Mills gap.
