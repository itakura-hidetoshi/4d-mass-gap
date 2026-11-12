# P4-Q2-PZ37AKH — original AJA no-go through the genuine AIM cubic cutoff

2026-11-12 JST. Formal mechanical-verification receipt; the record is not independently a theorem.

## Certification and provenance

- [PR #6674](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6674) MERGED; source `08389ba7c2bbc7d64710e94725384c6b6875c638`; formal squash `860375bd0605de89f4824ac42a140e3e06232b53`. Identical source/squash tree `96200fe3e144398cc6b69c8d777da43305b8d4b5`.
- [Exact-source CI #43143567948](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43143567948) and [formal push #43144248736](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43144248736) completed/SUCCESS including Lean job, step and independent completion receipt; 11,446/11,446 Lean; 7/7 declarations only standard `propext`/`Classical.choice`/`Quot.sound`; sorryAx 0; changed warning/error 0/0.
- One added theorem leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOutsideAILCubicAJANoGoV5_PZ37AKH.lean`; no original physical file edited.

## Exact scope

AIM's already proven cutoff `theta_H=(1/384)^n_H / (16*p_H+1)` is strictly larger than AKG's unchanged `tau_H`. Combining the ORIGINAL AIM all-boundary transfer inequality with the same genuine nonnegative top vector and unchanged AIW Haar budget B gives:

```text
0 < beta <= theta_H  =>  forall n:Nat, (9/4)*B_H,beta <= ||S^n f0||^2.
```

Hence there is NO strict original AJA power witness on the strictly additional band `tau_H < beta <= theta_H`. Any witness at beta>0 must have `beta>theta_H`; this is necessary, not sufficient. Neither the old fixed `beta0` nor all larger beta are decided by AKH alone.

No rank-one top, H-uniform coercivity, Hamiltonian spectral gap or continuum mass gap is inferred. Original Wilson/Haar/ZW/AJA unchanged; pinned Lean/mathlib and same-root append-only governance retained.
