# P4-Q2-PZ37AJS — original Wilson weighted one-step defect certificate

Date: 2026-11-11 JST. Status: **Lean4 formal proof verified and theorem PR merged**.

## Canonical source and provenance

- Repository: `itakura-hidetoshi/4d-mass-gap`.
- Canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
- Fixed Lean: `v4.30.0-rc2`; fixed mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Theorem PR: [#6633](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6633), squash MERGED.
- Exact certified source HEAD: `59c5a9759f60f043204dc406d0d021d7654ee3cf`.
- Source CI: [#42917279603](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42917279603), `completed/SUCCESS`.
- Source build: `11,433/11,433` completed successfully.
- Six declarations audited with `#print axioms`: one definition and five theorems; all only `propext, Classical.choice, Quot.sound`.
- No new `sorryAx`; zero changed-AJS Lean errors and warnings.
- Independent exact-source `completion receipt`: SUCCESS (event `pull_request`, exact SHA and run ID match).
- Canonical squash-merge HEAD: `8295e64a19cacb9d96945a2d5f603deed1ca314a`.
- Source and merged Git tree both: `64b050a125274b767c2ca7bd860a1abe2056a230`.
- Merged and certified AJS Lean blob: `de658374cf76f6a934640317f084d4a214a5d67c`.
- Merge push CI: [#42918264258](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42918264258), initially `in_progress`; certify separately on completion.

## Physical inputs retained

The leaf imports AJR and reuses AJQ's source reverse-Laplace lower bound, AIF's exact crossing Haar normalization, AIG's negative right-weighted original transfer-average bound, and AHN's true original source Haar second-moment floor.

For fixed finite spatial volume H and beta>0, define:

- `p_H` = original spatial plaquette count;
- `f_0` = original *centered physical ZW* source;
- `f_c` = the original AFZ continuous Haar representative of `f_0`;
- `W_H` = original spatial Wilson action;
- `T_H` = original complete one-slab SU(2) Wilson transfer, with both halfweights;
- `P_H` = original unnormalized physical transfer operator, and `S_H=P_H/||P_H||`;
- `V_H=∫ f_c(B)^2 dμ_H(B)` = original true Haar source second moment (AHN);
- `Z_cross(β)>0` = the exact genuine AIF crossing Haar partition.

## Exact new certified mathematics

The original positive source halfweight integral
`J_+(H,β) = ∫ exp(β W_H(B)/2) f_c(B) dμ_H(B)`
is bounded below by `β V_H` using AJQ's *opposite-sign* source Laplace estimate. No replacement source, sign flip of coupling, or modified transfer is introduced.

The original negative weighted right-boundary transfer-average
`A(H,β) = ∫ exp(β W_H(B)/2) T_H f_0(B) dμ_H(B)`
satisfies AIG's `A(H,β) <= -β Z_cross(β) exp(-β p_H) V_H`.

Define the genuine **weighted one-step defect scalar**

```
D_w(H,β) := ∫ exp(β W_H(B)/2) *
  (f_c(B) - ||P_H||^(-1) T_H f_0(B)) dμ_H(B).
```

AJS proves

```
D_w(H,β) = J_+(H,β) - ||P_H||^(-1) A(H,β),

β V_H + ||P_H||^(-1) β Z_cross(β) exp(-β p_H) V_H <= D_w(H,β),

0 < D_w(H,β),

β * (3 p_H/8)^2 * κ(1/96)^card(Link_H) <= D_w(H,β).
```

The last floor retains the **true**, strictly positive SU(2) Haar radius fraction `κ`, not a guessed decimal. The first lower bound uses both source and transfer, not just qualitative source nonvanishing.

Five new theorems plus one new definition are machine-checked; the full new source is the single 263-line file:

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedDefectQuantitativeV5_PZ37AJS.lean`

No existing Lean, physical model, coupling, measure, external assumptions, Lean/mathlib pins, formal root, or workflow was edited.

## What remains OPEN: strict hierarchy

The new scalar `D_w` is an integral of a *weighted* physical one-step difference. AJS does **not yet** prove an estimate identifying it with or bounding it by `||f_0-S_H f_0||` in the canonical physical Hilbert space. A separate exact L² representative bridge and a norm-duality/Cauchy–Schwarz inequality, using the **original** Haar probability, must be certified.

Until that bridge is proved, the prior AJR one-step inequality remains the available **independent** operator-norm certificate, but does not yield a new explicitly evaluated correction of the extra full-top residual by this AJS scalar.

Even after the bridge, the following need separate proofs/certificates: exact comparison with the real AJA strict budget, **concrete finite-power numerical witness**, sufficiently small added top residual, top eigenspace dimension one, unconditionally nonzero *transferred* excitation, finite-volume-uniform coercivity, Hamiltonian spectral gap, and 4D continuum Yang–Mills mass gap.

No inequality derived only at fixed H,β is silently upgraded to a volume-uniform or continuum theorem.

## Governance

append-only / tighten-only / overwrite-forbidden / same-root. This document is an append-only new formal proof record, not evidence for unproved continuum claims.
