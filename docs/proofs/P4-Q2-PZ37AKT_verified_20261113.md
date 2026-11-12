# P4-Q2-PZ37AKT — original fixed-beta0 strict AJA no-witness for every H<=16

Date: 2026-11-13 JST. Authoritative theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Mathematics and unchanged physical scope

The SAME original finite SU(2) Wilson physical one-slab operator
`P_(H,beta0)`, its original normalization `S=P/||P||`, the
signed centered ZW source `f0_H`, true spatial product Haar
probability `mu_H`, original AIG margin `m_H`, continuous
normalized source-transfer representative `u_H`, the actual
negative region `E_H={A:u_H(A)<-m_H}`, and exact original strict
AJA budget `B_H=m_H²*mu_H(E_H)` remain **unchanged**.

The original beta0=log(3/2)/64 and true
`p_H=24*(H+1)^3` are unchanged. AKS already proved
the genuine SU(2) one-link character has exact Haar second moment
1/4, and the genuine ORIGINAL crossing Haar partition obeys
`Z_H(beta)<=exp(p_H*(-beta+beta²/4))` at `0<=beta<=1`.
This is not a fictional Gaussian law or an independence
assumption about spatial plaquettes.

AKT uses existing exact AKO rational bounds
`0<beta0<=1/156` and `11/8<=log 4`.
For every natural H<=16, original p_H<=117912, hence
`beta0²*p_H/4<=11/8<=log 4`.

Because the ACTUAL original negative-region Haar mass
`r_H=mu_H(E_H)` is bounded by 1 by the original probability
measure, AKS's crossing estimate implies AKQ's ORIGINAL
partition-Haar sufficient test,
`r_H*Z_H(beta0)<=4*exp(-beta0*p_H)`.

The exact already-certified AKQ comparison then proves:
```text
forall (H : Nat), H<=16 ->
  NOT exists (n : Nat),
  || S_(H,beta0)^n f0_H ||² < B_(H,beta0).
```

This is a new **unconditional finite-volume no-witness theorem**,
including H=15 and H=16, with no numerical Haar mass input or
new physical assumption. A separate AKT theorem states H=16
explicitly. No H>=17 claim is proved by this leaf.

AKQ's underlying comparison establishes the non-strict original
budget/top implication whenever the AKT partition test holds.
The actual numerical `r_H` is still NO_DATA, and a strict sign
or equality decision for `B_H-||Qf0_H||²` has not been separately
certified by a new AKT declaration.

## Lean4 proof, exact source and reproducibility

New single file:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH16ExactCharacterMomentAJANoGoV5_PZ37AKT.lean`.

Five audited declarations:
1. `p4Q2PZ37AKT_originalPlaquetteCount_le_sixteen`.
2. `p4Q2PZ37AKT_originalFixedCoupling_quarterBudget_le_logFour`.
3. `p4Q2PZ37AKT_originalFixedCoupling_partitionHaarMass_of_le_sixteen`.
4. `p4Q2PZ37AKT_originalFixedCoupling_le_sixteen_no_AJA_power_witness`.
5. `p4Q2PZ37AKT_originalH16_no_AJA_power_witness`.

All declarations lie in
`MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`.

[AKT theorem PR #6706](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6706)
merged to the canonical formal theorem branch as
`8d9f8b7db2da7cb29b6506518f9f9d4b2ac561b0`.

Authenticated source HEAD:
`45a513f59d90aced02a4d1787e42c98bd81c954e`.

[Exact-source CI #43317972326](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43317972326)
completed **SUCCESS**. The actual pinned Lean dependency closure was
**11,455/11,455**. All 5/5 `#print axioms` results contained only
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
Changed AKT warning/error 0/0. Both the exact-source Lean job and
independent MCP completion receipt completed/SUCCESS.

Source HEAD, GitHub synthetic test-merge, and the integrated
squash share exactly Git tree
`2fef4b6d8ed7951cd2ef4a6d935124ab7cfa13be`.

The actual independent formal push
[CI #43318982017](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43318982017)
is assessed separately; its result is not assumed before completed
status and exact-head receipt are checked.

No past definition, theorem statement, fixed Lean
v4.30.0-rc2, pinned mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`,
published root, workflow or other file was altered.
Append-only / tighten-only / overwrite-forbidden / same-root.

## Outstanding independent tasks

H>=17 requires new rigorous quantitative bounds before claiming
witness existence or nonexistence. The finite-cell AKR program for
the actual r14 Haar mass remains separate and numerically unresolved,
even though AKS/AKT make it unnecessary for the no-witness result
through H16. Exact strict top/Haar residual, H-uniform GL source
Rayleigh bounds, Hamiltonian spectral gap and continuum
four-dimensional Yang--Mills mass gap remain OPEN.

The theorem canonical is formal; the public main branch must
receive only byte-identical proof-record mirroring and append-only
README/ROADMAP documentation, never a copy of Lean sources.
