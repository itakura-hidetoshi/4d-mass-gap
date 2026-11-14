# P4-Q2-PZ37ALU — original physical Wilson fixed-beta0 volume-step deficit variation

2026-11-15 JST. [Theorem PR #6755](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6755) **MERGED** to authoritative `formal/real-hilbert-uniform-coercive-strong-limit`, canonical squash `c45c3df5a4cde0a8744ed5ccb18bcc774c839a39`.

## Physical and mathematical scope

A single NEW append-only Lean4 leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0VolumeStepLossBudgetV5_PZ37ALU.lean`,
with **15 new declarations and 15 actual `#print axioms`**.

The true original physical SU(2) full-top-orthogonal normalized Wilson restrictions `R_H(beta0)` live in distinct H-dependent Hilbert spaces. ALU therefore NEVER subtracts `R_(H+1)-R_H` without a canonical carrier map. It works with the already-proven real scalar from ALN/ALT:
```text
delta_H = 1 - ||R_H(beta0)||² > 0
gap_H(beta0) >= delta_H/2
beta0 = log(3/2)/64
```

For every finite H define the **sharp minimal nonnegative one-step DOWNWARD loss** and cumulative variation,
```text
L_H = max(0, delta_H - delta_(H+1))
V_H = sum_{i=0}^{H-1} L_i.
```
ALU proves (without any new physical assumptions) `L_H >= 0`, its minimality for the one-step scalar inequality, `V_(H+1)=V_H+L_H`, monotonicity, the exact telescoping `delta_0<=delta_H+V_H`, and the genuine original-`beta0` physical bound
```text
delta_H >= delta_0 - V_H
gap_H(beta0) >= (delta_0 - V_H)/2.
```
A complementary obstruction certificate says if `delta_H<=r` then `V_H>=delta_0-r`.

The following **distinct premises remain UNPROVEN**:
1. `exists B < delta_0, forall H, V_H <= B`; OR
2. genuine nonnegative per-volume deficit-step upper bounds `b_H>=0`, `delta_H<=delta_(H+1)+b_H` with `forall H, sum_{i<H}b_i<=B<delta_0`.

Under either premise ALU formally constructs a positive H-independent gap `(delta_0-B)/2`. **No such budget for the original Wilson transfer is claimed, measured, or inferred from finite-volume compactness.** This is an explicit volume-step certificate route, not a proof of original-beta0 all-H mass gap. ALM's all-`s>8` Harnack cutoff obstruction remains.

## Exact-source machine verification and repair

- First proposed source `bc0895a88af9cc9fd5513abadf9d50e7ef4bb29a`; [CI #43627745510](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43627745510) **completed/SUCCESS**, genuine Lean **11,485/11,485**, all 15/15 public audits only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` absent, but **1** ALU warning on line 208: unused physical nonnegative-step-cost assumption `hb`. This initial source did not satisfy the zero-warning gate.
- Exact proof-only correction `28e4a62081ad61c47e8aafa0f02e8b5e15672ef7` uses `hb 0` and `htotal 1` to prove total cost budget `0<=B`. No theorem, hypothesis, or physical model change.
- Final [exact-source CI #43628524967](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43628524967) **completed/SUCCESS**, actual pinned Lean **11,485/11,485**, **15/15** standard-three `#print axioms`, `sorryAx` absent, ALU warning/error **0/0**, independent exact-source completion receipt completed/SUCCESS.
- Source, synthetic test merge, and canonical squash HEAD `c45c3df5a4cde0a8744ed5ccb18bcc774c839a39` have exact Git tree `1c63d76800fb8119a7ac0b02431d264a387b38d9`.
- Independent canonical event=push CI [#43629063478](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43629063478) **in progress at this initial record snapshot**. Do not infer its result from the successful PR CI; append a verified completion receipt after actual job and independent exact-canonical-HEAD receipt finish.

## Next OPEN work

An actual original-`beta0` Wilson/Haar estimate controlling downward variation `V_H` or suitable summable physical one-step costs `b_H` is NOT YET PROVED. Finite-volume carrier compatibility or a genuine two-scale transport law would be needed for a more analytic cost estimate. Hamiltonian and continuum 4D Yang–Mills mass gaps remain OPEN.

Original physical SU(2) Wilson P, normalized S, true top sector K, Haar/AJA, the prescribed beta0, all existing sources, Lean v4.30.0-rc2 and mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 are unchanged. Append-only / tighten-only / overwrite-forbidden / same-root.

## Independent canonical push — final completed receipt (2026-11-15 JST)

The preceding independent-push PENDING snapshot was the correct status when this record was first written. Direct GitHub MCP re-observation has now established [canonical push CI #43629063478](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43629063478) **completed/SUCCESS** at the exact canonical formal HEAD `c45c3df5a4cde0a8744ed5ccb18bcc774c839a39`. The changed-Lean job `132551377886` completed SUCCESS; real pinned Lean dependency closure **11,485/11,485**; actual 15/15 ALU public axiom audits use only `propext`, `Classical.choice`, `Quot.sound` with no sorryAx; changed ALU warning/error **0/0**. Independent completion receipt job `132553111562` completed SUCCESS, emitting `[mcp-receipt] event=push exact_sha=c45c3df5a4cde0a8744ed5ccb18bcc774c839a39 source_result=success run=43629063478 attempt=1`. GitHub exact-head status SUCCESS. Source, synthetic test-merge, canonical squash tree equality remains `1c63d76800fb8119a7ac0b02431d264a387b38d9`. No original Wilson all-volume bound or continuum mass gap follows from this CI result.
