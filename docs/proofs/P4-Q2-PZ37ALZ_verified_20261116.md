# P4-Q2-PZ37ALZ — verified original-beta0 linear relative-error telescoping

2026-11-16 JST. [Theorem PR #6768](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6768) **MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit`, canonical commit `4e0f4d894dfab5f4ebc426b946052db825ca6c6d`.

## Conditional mathematics and preserved physical obstruction

One NEW append-only Lean leaf, **250 lines added and 7/7 individually audited declarations**:

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0LinearRelativeErrorBudgetV5_PZ37ALZ.lean`

ALY gives `r_(H+1)<=r_H+t_H` for the actual original fixed-beta0 true Wilson normalized excited operator norms `r_H=||R_H||`, under independently required physical scaled raw/full scalar inequalities. ALZ telescopes **LINEAR** costs before squaring:

```text
r_H<=r_0+sum_{i<H}t_i,
sum_{i<H}t_i<=T for all H,  r_0+T<1
⇒ delta_H=1-r_H²>=1-r_0-T>0
⇒ gap_H>=(1-r_0-T)/2>0.
```

A finite-prefix/tail criterion begins at any M. ALT unconditionally handles each finite H<=M; if `sum_{i<n}t_(M+i)<=T` for all n and `r_M+T<1`, then a common all-H positive gap follows. The geometric **relative-error** tail hypothesis `t_(M+n)<=C*rho^n` with `C>=0`, `0<=rho<1`, `C<(1-rho)*(1-r_M)` is sufficient. This linear summation can be less wasteful than independently summing ALY's `2t_i+t_i²` at each volume.

The ratio comparisons and the small summable cost are **not provided for the physical Wilson model**. All operators `P_H,A_H,R_H`, Haar/AJA, gauge-invariant Hilbert carriers, actual prescribed `beta0=log(3/2)/64`, normalization, public roots and toolchain pins are unchanged. No subtraction/identification of differently typed H-Hilbert operators. A conditional theorem does not certify the premise it assumes.

## Exact machine provenance

- Source HEAD `2a9a4ec7c047fe3a722b41f00d4d1cac6c2d516f`; new leaf Git blob `7f29431222b0417c8ce8978ec1e3fe7f2f439bee`; 7 `#print axioms` entries.
- ALY parent repair `3ecdfd60aa339f8fc463708d8ad24c1298f5c504` incorporated via the source's true two-parent history. The PR adds **only the new ALZ Lean file** relative to the parent.
- [Exact-source PR CI #43676467795](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43676467795) **completed/SUCCESS**, pinned Lean **11,490/11,490**, 7/7 new ALZ public `#print axioms` prints depend only on `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, ALZ warning/error 0/0. Exact-HEAD completion receipt job `132744477747` SUCCESS.
- Source, synthetic test merge, and **actual authoritative merge** share identical Git tree `1f3227d815b37d39909d0a509c1092ae0f74bc3c`. Canonical merge `4e0f4d894dfab5f4ebc426b946052db825ca6c6d`.
- Independent *postmerge* [push CI #43693765510](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43693765510) **completed/SUCCESS** at that exact canonical HEAD, `11,490/11,490` full dependency closure, original ALY 15/15 + ALZ 7/7 standard-three axiom audits, no `sorryAx`, no changed warnings/errors. Changed Lean job `132750063860` and independent exact-HEAD receipt job `132783704522` both SUCCESS:

```text
[mcp-receipt] event=push exact_sha=4e0f4d894dfab5f4ebc426b946052db825ca6c6d source_result=success run=43693765510 attempt=1
```

- Fixed Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## Next physical task

Obtain independently proved physical original Wilson cross-volume scale comparisons and relative `t_H` estimates with summable tail below the strict `1-r_M` margin. In particular, the freedom to choose a common scalar `s_H` must NOT be mistaken for a physical mixing/decay estimate. Without the genuine model-specific estimate the original fixed-beta0 all-H spectral gap, Hamiltonian gap, continuum four-dimensional Yang–Mills mass gap remain **OPEN/NO_DATA**.

See [ALY proof record](P4-Q2-PZ37ALY_verified_20261116.md) for failed-run provenance, normalization identity and independent combined canonical push certificate.
