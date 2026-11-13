# P4-Q2-PZ37AKY — genuine H=22 complementary Haar-cell descent

2026-11-13 JST. Authoritative theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
This proof record documents the verified **conditional** H22 complement-cell interface. It does not certify a numerical upper mass bound.

## 1. Preserved original physical objects

The theorem reuses without modification the true SU(2) Wilson one-slab physical transfer `P`, existing normalized `S=P/||P||`, the original signed centered ZW source `f0`, true spatial product Haar probability `mu22`, the original AIW pointwise normalized transfer `u22`, unchanged AIG margin `m22`, original strict negative event `E22={A:u22(A)<-m22}`, original AJA budget `B22=m22²*mu22(E22)`, and the genuine full-top orthogonal projection `Q`. The original coupling is `beta0=log(3/2)/64`, with exact `p22=292008`.

The AKW/AKX genuine Haar-MGF criterion is
```
r22 * exp((44/351)*beta0²*292008) <= 4
where r22 = mu22(E22).
```
The numerical threshold `r22<=4*exp(-(44/351)*beta0²*292008)` is about 0.9204180158. This decimal is **not** a measured or proved original Haar mass.

## 2. Nine certified declarations

One new Lean4 file only:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH22ComplementBorelDescentV5_PZ37AKY.lean`.
Exact public declarations in `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`:

1. `p4Q2PZ37AKY_originalH22_negativeEvent_measurable`: actual original H22 strict negative event is measurable.
2. `p4Q2PZ37AKY_originalH22_negativeHaarMass_ge_half`: true `r22>=1/2` from existing AIT+AIW, a **lower** bound only.
3. `p4Q2PZ37AKY_originalH22_complementHaarMass_le_half`: true `mu22(E22^c)<=1/2`.
4. `p4Q2PZ37AKY_originalH22_negativeHaarMass_le_of_rationalCells`: for measurable pairwise-disjoint original H22 cells `Ci` with certified rational pointwise `li<=u22(A)` on every `A in Ci`, `li>=-m22`, and independently certified true Haar lower masses `qi<=mu22(Ci)`, prove `r22<=1-sum qi`.
5. `p4Q2PZ37AKY_originalH22_certifiedCellTotal_le_half`: valid original H22 complementary-cell Haar lower sums cannot exceed 1/2.
6. `p4Q2PZ37AKY_originalH22_massThreshold_of_rationalCells`: if additionally `sum qi >= 1-4*exp(-(44/351)*beta0²*292008)`, infer the exact AKX original mass threshold.
7. `p4Q2PZ37AKY_originalH22_no_AJA_of_rationalCells`: under those same verified cell assumptions, no original strict finite-power AJA witness exists.
8. `p4Q2PZ37AKY_originalH22_budget_le_fullTop_of_rationalCells`: under the same conditions, `B22<=||Qf0_22||²`.
9. `p4Q2PZ37AKY_originalH22_delta_nonpos_of_rationalCells`: under the same conditions, `Delta22=B22-||Qf0_22||²<=0`.

No actual cell collection, rational transfer enclosure or actual original Haar lower mass table was constructed; the hypotheses remain explicitly visible. The complement target is about 0.0795819842, not a certificate. A true lower bound `r22>=1/2` is compatible with, but does not imply, the required upper bound.

## 3. Exact-source machine authentication and provenance

[Theorem PR #6721](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6721) **MERGED**.
Final exact-source HEAD: `549a9e14087a340c24a83dd49c5569a5d880bf5e`.
Canonical theorem squash: `f34fc3334decf7d2e525cffd05878b17948e0890`.
Source / synthetic test-merge / canonical squash identical Git tree:
`ee881a351fa32fa78f909673a6bb698c7b690d25`.
Canonical theorem squash has the prior formal HEAD
`2140c9747480407318b2c7a5f2b27bca6f952e5f` as its sole parent.

[Exact-source CI #43369969692](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43369969692)
completed/**SUCCESS** (event pull_request, attempt 1, final HEAD above).
Real Lean build **11,461/11,461** successful; all nine individual `#print axioms` actual outputs are only `propext`, `Classical.choice`, `Quot.sound`; new sorryAx absent, AKY file warning/error **0/0**.
Main Lean job `131703250486` completed/SUCCESS.
Independent exact-head completion receipt job `131705658212` completed/SUCCESS, logged
```
[mcp-receipt] event=pull_request exact_sha=549a9e14087a340c24a83dd49c5569a5d880bf5e source_result=success run=43369969692 attempt=1
```
and published GitHub status `chatgpt-ci-receipt/PR Lean Fast Check = success`.
The first source HEAD `fa874c6f79ceb16a280c808733ceee28ed01297f` had a superseded CI; the final second source update made the measurable-event theorem public and included its independent ninth axiom print. Final authentication refers **only** to the latest successful HEAD.

Independent *canonical formal branch push CI* [#43370875467](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43370875467) is separately monitored. Its success must be independently established and appended **after** its completed exact-head receipt. This paragraph is not a pre-certified push result.

Pinned Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. New Lean module only; no existing physical definition, imported theorem statement, hypotheses, old Lean source, public root, CI workflow or dependency pin changes. Append-only / tighten-only / overwrite-forbidden / same-root.

## 4. Remaining obstruction and next physics

The real H22 source-transfer lower enclosure on **every configuration** of proposed complementary Borel cells, genuine normalized SU(2) product-Haar lower masses, valid pairwise-disjointness/measurability and a total lower mass above the exact target are **NO_DATA**. In particular, no positive-side cell existence is inferred from the lower-half negative-region theorem; no global complement is constructed from isolated local observations.

Independent physical alternatives include a true H22 transfer-sign or second-moment inequality and stronger genuine physical norm/overlap comparison; these require new original-model proofs, not replacement Gaussian measures or fabricated mass tables.

Unconditional H22 no-AJA, strict Delta22 negativity/equality, H>=23, H-uniform Gauss-law coercivity, Hamiltonian spectral gap and continuum four-dimensional Yang–Mills mass gap remain **OPEN**.

Docs-only formal and main changes do not replace exact-source Lean CI. Mirror this identical proof-record blob to main only after the formal documentation integration is certified.


## 5. Independent canonical formal-squash push authentication (2026-11-13 JST)

The historical pending-status paragraph above is retained as the original state at draft creation. Canonical formal squash `f34fc3334decf7d2e525cffd05878b17948e0890` independently passed its actual [formal push CI #43370875467](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43370875467), completed/**SUCCESS**, event=push. The changed Lean job `131706055882` completed/SUCCESS with pinned **11,461/11,461** build and all **9/9** AKY declaration axiom outputs restricted to `propext`, `Classical.choice`, `Quot.sound`; new sorryAx absent, AKY warning/error **0/0**. The independent exact-head completion receipt job `131708103665` completed/SUCCESS and logged `[mcp-receipt] event=push exact_sha=f34fc3334decf7d2e525cffd05878b17948e0890 source_result=success run=43370875467 attempt=1`, with published commit status `success`. Integrated Git tree `ee881a351fa32fa78f909673a6bb698c7b690d25` matches certified source and synthetic test-merge. The actual H22 numerical Haar upper bound remains **NO_DATA**; all cell descent statements are conditional.
