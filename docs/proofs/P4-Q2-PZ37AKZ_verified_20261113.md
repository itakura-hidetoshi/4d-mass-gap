# P4-Q2-PZ37AKZ — stepwise genuine H22/H23/H24/H25 original AKX threshold frontier

2026-11-13 JST. Canonical theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
This record distinguishes *scalar sufficient-test feasibility*, *actual original Haar-mass certification* and *true AJA finite-power witness existence*.

## 1. Original physical scope

Exactly the existing finite-volume SU(2) Wilson one-slab physical transfer, `S=P/||P||`, centered signed ZW source `f0_H`, normalizing physical norm, AIG strict negative margin, continuous normalized source `u_H`, true product SU(2) spatial Haar `mu_H`, full-top eigenspace projection `Q_H`, and AJA budget are retained. The unchanged fixed coupling is `beta0=log(3/2)/64`, and original plaquette count is `p_H=24*(H+1)^3`.

Define exact AKX quantities:
```
r_H := mu_H {A : u_H(A) < -m_H}
q_H := (44/351)*beta0^2*p_H
T_H := 4*exp(-q_H).
```
AKX proves that `r_H<=T_H` suffices for original AJA strict finite-power no-witness, `B_H<=||Q_H f0_H||²` and `Delta_H<=0`. AKZ does not replace this with a claim of equivalence or guarantee that r_H satisfies the sufficient inequality.

## 2. Stepwise result and the exact obstruction

The original AIT/AIW results certify `r_H>=1/2` for every finite H at the fixed beta0.

AKZ proves `q_H<log 8` and hence `1/2<T_H` for **every H<=24**. In particular the original fixed-volume H=22, H=23, and H=24 checks are three individual public Lean theorems. These statements establish logical compatibility with the r_H lower bound, **not actual upper mass data**. Actual r_22, r_23 and r_24 upper values are **NO_DATA**.

AKZ also proves `log 8<q_H` and `T_H<1/2<=r_H` for **every H>=25**. Thus `not (r_H<=T_H)` holds unconditionally in the true original model for H>=25. The original H=25 instance is separately theorem-checked. This is a rigorous **failure of a sufficient-test premise**, not proof that an AJA witness exists, not positive Delta, and not physical Hamiltonian/continuum mass gap information.

For numerical orientation only (not measured Haar values):
| H | exact original p_H | approximate scalar T_H | conclusion |
|---|---:|---:|---|
| 22 | 292008 | 0.9204180 | permitted, actual r22 upper NO_DATA |
| 23 | 331776 | 0.7535064 | permitted, actual r23 upper NO_DATA |
| 24 | 375000 | 0.6062294 | permitted, actual r24 upper NO_DATA |
| 25 | 421824 | 0.4789835 | AKX sufficient test formally excluded |

The exact check does **not** rest on these decimals.

## 3. Rational and machine-checkable proof mechanism

Instead of a floating-point estimate, pinned Mathlib `Real.exp_bound` at n=3 on `201/500` proves `exp(201/500)<=3/2`, hence `log(3/2)>=201/500` and the **exact genuine** fixed coupling `beta0>=201/32000`.

Pinned `Real.log_two_gt_d9` and `Real.log_two_lt_d9` give the rational bracket `2<log8<52/25`.
The certified existing `beta0<=1/156` and original count `p_H<=375000` for H<=24 imply `q_H<2<log8`.
The new lower bound `beta0>=201/32000` and count `p_H>=421824` for H>=25 imply `52/25<q_H`.
The inequalities transport through monotonic `Real.exp` to the corresponding threshold relations. No numerical integral, Monte Carlo or Haar-probability proxy is introduced.

## 4. Exact-source authentication

New append-only Lean module:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH22ToH25StepwiseThresholdFrontierV5_PZ37AKZ.lean`.
Sixteen public declarations, each with one fully qualified `#print axioms` audit.

[PR #6724](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6724) MERGED.
Exact-source HEAD `6ad1f350dd1c9b38ee68184e154a74ee8cd4821e`.
Authoritative squash `9b42d878487e8cf435d660a7ded4657803b9a477`.
Original source, GitHub synthetic test-merge, and actual squash tree all equal
`116fb9e131306f89d56d627bd5b0f392df846ce5`.

[Exact-source CI #43376033297](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43376033297), attempt 1, completed/SUCCESS. Genuine Lean dependency closure **11,462/11,462**, sixteen of sixteen actual `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`; new sorryAx none; AKZ changed warning/error 0/0. Main Lean job `131722627035` completed/SUCCESS. Separate receipt job `131725392841` completed/SUCCESS and logged
```
[mcp-receipt] event=pull_request exact_sha=6ad1f350dd1c9b38ee68184e154a74ee8cd4821e source_result=success run=43376033297 attempt=1
```
with published GitHub commit status SUCCESS.

The independently triggered authoritative formal push [CI #43377047107](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43377047107) remains a separate check. This initial record does not pre-certify the push result; append its exact SHA completion receipt once completed.

Fixed Lean `v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. All original physical definitions, hypotheses, earlier Lean sources, roots, workflows and pins unchanged. append-only / tighten-only / overwrite-forbidden / same-root.

## 5. Next unresolved mathematics

At H=22,23,24, separately construct quantitative genuine original Haar complement certificates or stronger original operator/top projection estimates. An interval `1/2<=r_H` with `1/2<T_H` **does not** yield `r_H<=T_H`. At H>=25 the AKX criterion is proved impossible, so a *different* sufficient inequality, potentially built from a stronger true physical norm / Ward / top-sector comparison, must be established before a no-witness conclusion is possible. The obstruction must not be hidden by inductive extrapolation. Strict Delta, H-uniform coercivity, Hamiltonian spectral gap, continuum four-dimensional Yang-Mills mass gap all OPEN.


## 6. Independent authoritative formal-push completed verification (2026-11-13 JST)

The original pending-status paragraph above is preserved as a historical snapshot. Canonical AKZ theorem squash `9b42d878487e8cf435d660a7ded4657803b9a477` independently passed actual [formal push CI #43377047107](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43377047107), completed/**SUCCESS**. Genuine pinned Lean dependency closure **11,462/11,462**; all **16/16** AKZ declarations' `#print axioms` are limited to `propext`, `Classical.choice`, `Quot.sound`, no new sorryAx, changed AKZ warning/error **0/0**. Independent push CI main job `131725856870` completed/SUCCESS and exact-head completion receipt job `131728298910` completed/SUCCESS, logging `[mcp-receipt] event=push exact_sha=9b42d878487e8cf435d660a7ded4657803b9a477 source_result=success run=43377047107 attempt=1`, with GitHub commit status `success`. Original theorem source, synthetic test-merge and integrated squash tree are all `116fb9e131306f89d56d627bd5b0f392df846ce5`. This authenticates scalar-test feasibility for H<=24 and its contradiction with genuine r_H>=1/2 for H>=25; it does NOT provide actual r22/r23/r24 upper bounds, AJA witness existence, or Hamiltonian/continuum mass gaps.
