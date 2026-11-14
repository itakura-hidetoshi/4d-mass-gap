# P4-Q2-PZ37ALT — certified original fixed-beta0 finite-prefix physical gap and conditional tail descent

2026-11-15 JST. Authoritative theorem branch `formal/real-hilbert-uniform-coercive-strong-limit`.
[Theorem PR #6754](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6754) **MERGED**.
Fixed original SU(2) Wilson transfer/Haar/AJA/model definitions are unchanged; original `beta0=log(3/2)/64` is NOT replaced by the separate high-temperature `betaStar`.

## Genuine new Lean4 results

One new 213-line Lean source:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0FinitePrefixTailDescentV5_PZ37ALT.lean` (11 new declarations and 11 `#print axioms` audits).

For **each** finite original physical Wilson volume H, the existing ALN theorem certifies the exact scalar squared defect
```text
delta_H = 1 - ||R_H(beta0)||^2 > 0
```
for the normalized full-top-orthogonal transfer. ALT proves the exact factorization
```text
delta_H = (1 + ||R_H(beta0)||) * gap_H(beta0)
gap_H(beta0) >= delta_H/2 > 0.
```

For every **fixed finite** M, the new recursively defined exact floor
```text
d_M = min_{0 <= H <= M} delta_H > 0
forall H <= M, gap_H(beta0) >= d_M/2 > 0
```
is **unconditional** in the unchanged physical Wilson model. It makes no unjustified independence claim about M.

For global descent, ALT introduces an explicitly **unproved** model-specific tail premise: for **every H > M** and physical full-top-orthogonal x, the actual original raw Wilson operator obeys
```text
||P_H(beta0) x|| <= q * F_H(beta0) * ||x||
with 0 <= q < 1,
```
where F_H is the genuine positive ALJ/ALI moment-based lower floor on the physical norm. Under this extra premise alone, ALT constructs
```text
forall H, gap_H(beta0) >= min(d_M/2, 1-q) > 0.
```
The tail premise is not proved. ALN/ALO also show that the F_H-scaled test is stronger than the exact raw test with the true `||P_H||`; this condition must NOT be assumed automatically from finite-volume strict contraction.

## Exact-source repair and machine certification

- Initial research HEAD `0f28ed282916aaf08321125f012bf6d2b5506660`, [CI #43611827912](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43611827912) **completed/FAILURE**. The full new ALT source, ALN/ALS source, imports, and fixed mathlib patterns were checked. Exactly one direct error arose at line 200: `end MGAP4D.MathlibAnalytic` while the unnamed `noncomputable section` was still open. All 11 declarations had elaborated with standard-three axiom prints; the failure was scope closure, not invalid mathematics.
- Fix: add one anonymous `end` before the final named namespace `end`. No theorem statement/assumption, physics, import, or old Lean file changed. Exact corrected source HEAD `06d35cbb3dba550152c64c39a1abb3ce103292da`.
- [Exact-source CI #43612424066](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43612424066) **completed/SUCCESS**; fixed Lean **11,484/11,484**. All **11/11** new ALT audits only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, changed ALT warning/error **0/0**, exact-head independent completion receipt success.
- Formal canonical expected-head squash commit `e251dad5b8059e9e1d35c1a67e4629c373f47058` shares exact Git tree `9fcfbb150f2662f2b474b49ef9916ad7abfd7964` with corrected source and synthetic test merge.
- [Independent canonical push CI #43613074250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43613074250) **completed/SUCCESS**, genuine pinned **11,484/11,484**, **11/11** ALT audits standard three, no new `sorryAx`, changed warning/error **0/0**, independent exact-canonical-HEAD receipt **SUCCESS**.

## Open large-H obstruction

ALM proves every existing s>8 high-temperature certificate cutoff is below actual beta0. ALT does not weaken this no-go. The finite-prefix d_M can decrease to zero as M grows; ALT neither proves nor assumes a common positive lower bound over all M. At a future stage, a genuine large-volume estimate (direct raw Wilson tail, or an independent volume-step loss budget) is required. There is **no unconditional all-H fixed-beta0 spectral gap**, Hamiltonian mass gap, or 4D continuum Yang–Mills mass-gap theorem here.

Operating rules: append-only / tighten-only / overwrite-forbidden / same-root. Pinned Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
