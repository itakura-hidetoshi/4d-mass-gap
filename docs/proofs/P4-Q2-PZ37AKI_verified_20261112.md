# P4-Q2-PZ37AKI — all-positive genuine Ward affine top floor and logarithmic no-witness cutoff

2026-11-12 JST. This is the explanatory record for the kernel-checked formal Lean source.

## Actual receipts

- [PR #6675](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6675) MERGED. Certified source `e89795f308a2383f4b8c46c2a7a35fae4247631d`; formal squash `b0c7011010a7a63feefa7b76c0581d532be81574`; common source/squash Git tree `1d2e1bc49369021236d56b36c5f13fc31d1f69a9`.
- [Exact-source CI #43148059365](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43148059365) and independent [formal push #43148760017](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43148760017): completed/SUCCESS including workflow, Lean step and separate completion receipt; 11,447/11,447 Lean; 13/13 declarations audited; only `propext`, `Classical.choice`, `Quot.sound`; sorryAx 0, changed warning/error 0/0.
- New leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWardAffineLogarithmicAJANoGoV5_PZ37AKI.lean`; 3 auxiliary scalars and 10 theorems; no changes to old files, original models or hypotheses.

## Verified theorem and its boundary

Original Ward half-Haar inequality gives an actual affine bound `P f0(B)<=c_H,beta*f_c(B)-d_H,beta`, with `c=Zcross*exp(-beta*p)*r(beta)^4`, `d=beta*exp(-3*beta*p)*V>0`. With the existing nonnegative Wilson top eigenvector and norm normalization, `<f0,psi> <= -d` and hence `||S^n f0||^2>=d^2` for all beta>0 and n:Nat.

For the original AJA B, `B<=(beta*exp(-beta*p)*V/2)^2`. Thus with `kappa_H=log(2)/(2*p_H)`:

```text
0 < beta <= kappa_H => NOT exists n:Nat, ||S^n f0||^2 < B_H,beta.
```

The comparison `theta_H<kappa_H` is formalized. For the actual fixed `beta0=log(3/2)/64` the no-witness conclusion is proved at **H=0**, not for every H. Outside the logarithmic cutoff this theorem alone cannot decide witness existence or nonexistence.

Top simplicity, uniform H coercivity, Hamiltonian and 4D continuum mass gap remain OPEN. Original physical data and pinned Lean/mathlib unchanged.
