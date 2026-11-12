# P4-Q2-PZ37AKU — original H<=16 Haar-budget/full-top residual nonpositivity

Date: 2026-11-13 JST. Authoritative theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Original-model result and exact scope

Keep the original complete finite SU(2) Wilson one-slab physical
operator P, its original normalized S=P/||P||, the true full-top
eigenspace projection Q, the original ZW centered signed physical
source f0_H, normalized product Haar measure mu_H, AIG negative
margin m_(H,beta), original continuous normalized transfer
representative u_(H,beta), and original strict AJA budget
`B_(H,beta)=m_(H,beta)^2 * mu_H{u_(H,beta)<-m_(H,beta)}`.

The original fixed coupling beta0=log(3/2)/64, original plaquette
count, Wilson kernel and all prior hypotheses/definitions are unchanged.

AKQ previously established that the genuine weighted physical
partition-Haar condition
`r_H * Z_H(beta)^2 <= 4*||P_(H,beta)||` implies the exact
**ORIGINAL** budget/top energy bound
`B_(H,beta)<=||Q f0_H||²`.
The AIF partition Z_H, original physical norm and true Haar mass
r_H are not changed or replaced.

AKU proves that the weaker original partition-Haar condition
`r_H*Z_H(beta)<=4*exp(-beta*p_H)` also implies this ORIGINAL
budget/top bound by the original AIW spatial-mean norm estimate.
The now-certified AKT result discharges that condition for
every H<=16 at the unchanged fixed beta0. Therefore:

```text
for all H : Nat, H<=16:
B_(H,beta0) <= ||Q_(H,beta0) f0_H||²
Delta_H := B_(H,beta0) - ||Q_(H,beta0) f0_H||² <= 0
```

An explicit H=16 theorem certifies this same original residual.
This is **unconditional** at those finite volumes.
No actual numerical r_H is assumed, measured or inferred.

Only the non-strict inequality `Delta_H<=0` is proved.
AKU does **NOT** establish `Delta_H<0` or `Delta_H=0`.
These alternatives remain unresolved. The earlier notation
`Delta_H sign=NO_DATA` must now be refined:
`Delta_H<=0` is machine-certified on H<=16, while strictness
or equality is NO_DATA. H>=17 is not included.

## Lean4 source and independent audit

New append-only Lean source:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH16HaarBudgetTopResidualV5_PZ37AKU.lean`.

Four certified declarations in
`MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`:

1. `p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass`
2. `p4Q2PZ37AKU_originalFixedCoupling_budget_le_fullTop_of_le_sixteen`
3. `p4Q2PZ37AKU_originalFixedCoupling_topHaarResidual_nonpos_of_le_sixteen`
4. `p4Q2PZ37AKU_originalH16_topHaarResidual_nonpos`

[AKU theorem PR #6709](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6709)
MERGED to canonical formal, integrated commit
`468196fa09489101b857d65d054dd0d3c2ecbae1`.

Authenticated exact-source HEAD:
`d5879fde1935ba140fbd0e5f942ceee3242d7574`.

[Exact-source CI #43320891189](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43320891189)
completed **SUCCESS**, pinned Lean dependency closure **11,456/11,456**.
All 4/4 `#print axioms` lines report only the standard
`propext`, `Classical.choice`, `Quot.sound`;
new `sorryAx` absent, AKU changed-file warning/error 0/0,
and the independent exact-head completion receipt completed/SUCCESS.
Source, synthetic test-merge and canonical squash have the same
Git tree `8b5026f5c6861e5d9787c443f9771a3884b5c60b`.

The independently triggered actual formal squash push
[CI #43321778660](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43321778660)
is separately monitored; do not pre-certify its completion.

This one-file addition changes no prior theorem statement, original
Wilson/Haar/ZW source, pinned Lean v4.30.0-rc2, pinned mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`,
published root or CI workflows.
Append-only / tighten-only / overwrite-forbidden / same-root.

## Remaining boundary

Strict negativity or equality of Delta_H on H<=16,
actual r_H values, H>=17 top–Haar comparisons,
H-uniform GL Rayleigh floor, Hamiltonian spectral gap and
continuum 4D Yang--Mills mass gap are not proved.
The separate AKR finite Borel cell mass-value program remains
open even though the non-strict budget/top comparison now holds
without it through H16.

Canonical Lean only on formal; docs-only main mirror must use an
identical proof-record blob and append README/ROADMAP without
replacing prior material.


## Independent canonical formal-push certification (2026-11-13 JST)

The separately triggered, actual canonical squash-push [CI #43321778660](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43321778660) for exact formal HEAD `468196fa09489101b857d65d054dd0d3c2ecbae1` has now completed **SUCCESS** (event `push`, run attempt 1). The first job, `Changed Lean fast check` (`131543987497`), completed **SUCCESS** and built the pinned dependency closure **11,456/11,456**. The four AKU `#print axioms` declarations each use only `propext`, `Classical.choice`, `Quot.sound`; new `sorryAx` absent, modified AKU warning/error **0/0**.

The independent `Publish MCP CI completion receipt` job `131547094006` completed **SUCCESS**. Its execution log records `event=push`, `exact_sha=468196fa09489101b857d65d054dd0d3c2ecbae1`, `source_result=success`, `run=43321778660`, `attempt=1`. The independent GitHub commit status is `success` (`chatgpt-ci-receipt/PR Lean Fast Check`) on that exact SHA. Actual canonical commit Git tree `8b5026f5c6861e5d9787c443f9771a3884b5c60b` equals the previously authenticated source/test-merge/squash tree. The earlier monitored/not-yet-certified wording above is preserved as its historical pre-completion state; this later record certifies completion.

This independent verification adds no stronger physics theorem. For H<=16 only, `B_(H,beta0)<=||Qf0_H||²` and `Delta_H<=0` are certified; `Delta_H<0` versus equality is **NO_DATA**, and H>=17, true Haar numerical mass, H-uniform Rayleigh, Hamiltonian/continuum mass gaps remain **OPEN**. This docs-only append preserves the original Wilson definitions, signed source, Haar measure, AJA budget, pinned Lean/mathlib and canonical root.
