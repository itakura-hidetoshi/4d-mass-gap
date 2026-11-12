# P4-Q2-PZ37AKG — original Wilson small-coupling AJA witness no-go

2026-11-12 JST. **Proof record, not a new proof.** Formal source is exclusively `formal/real-hilbert-uniform-coercive-strong-limit`; main carries docs-only mirror.

## Exact-source and independent integration

- [Theorem PR #6673](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6673) MERGED; certified source `a543dfebcfabbc3d34ae48deda1f9d2326573927`, formal squash `7e86f90bb6075dcd5d6a5494f8c1982b599f18d5`, identical source/squash Git tree `fa6b45c039604fbf61b6e0b2145570ea1b251ff2`.
- [Exact-source CI #43127198792](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43127198792), [independent formal push CI #43128076902](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43128076902): workflow, Lean job, Lean step and independent completion receipt completed/SUCCESS. 11,445/11,445 Lean, 11/11 kernel axiom audits standard `propext`, `Classical.choice`, `Quot.sound`, no new sorryAx, changed AKG warning/error 0/0.
- One new 384-line Lean leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSmallCouplingAJAWitnessNoGoV5_PZ37AKG.lean`. Initial run #43124580243 failed on a Lean product-measure notation and typed real-inner scalar rewrite; corrections touched only the new leaf proof.

## Certified mathematical scope

For genuine finite H and `0 < beta <= tau_H`, where `tau_H = v_H / (16*p_H^3 + 1)>0` is the unchanged AIL cutoff, the *original* symmetric Wilson P, S=P/||P||, signed centered ZW source f0, original Haar negative-margin certificate B>0 satisfy, **for every n : Nat**:

```text
(9/4)*B_H,beta <= ||S_H,beta^n f0,H||^2
```

Thus the original strict finite-power AJA witness does **not** exist on this interval. In particular beta=tau_H supplies an actual finite-H coupling counterexample to the assertion that such a witness exists for all beta>0. Proof uses the original nonnegative unit top eigenvector but does **not** assume that the entire top eigenspace is one-dimensional.

No assertion outside the cutoff, no Hamiltonian or 4D mass-gap conclusion. All existing Wilson/Haar/ZW/AJA definitions, formal root, Lean `v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` preserved. Append-only / tighten-only / overwrite-forbidden / same-root.
