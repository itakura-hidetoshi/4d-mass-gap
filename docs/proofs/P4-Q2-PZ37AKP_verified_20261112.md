# P4-Q2-PZ37AKP — exact fixed-beta0 frontier for the original AKN quadratic criterion

Date: 2026-11-12 JST. Sole canonical theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Exact preserved model and logic

Keep the genuine original finite-H SU(2) Wilson physical one-slab P,
S=P/||P||, signed centered ZW source f0, top projection Q, true
spatial halfweight and Haar probability, normalized source u, unchanged
original margin m, and original negative-region Haar budget B.

AKN proves *absence* of a strict original AJA finite-power witness
if beta>0 and `beta^2 * p_H / 2 <= log 4`. AKO proves the
unchanged original `beta0=log(3/2)/64` satisfies that sufficient
**no-witness** criterion for every `H<=13`.

AKP identifies the *exact applicability frontier of that scalar test*.
It does **not** identify the actual existence or absence of an AJA witness
outside the criterion, and does not prove or disprove the 4D mass gap.

## Six new kernel-certified declarations

One append-only new Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticFrontierV5_PZ37AKP.lean`.

1. The lower tangent `1-x⁻¹<=log x` at the three positive rational
   factors `7/6`, `8/7`, `9/8`, whose product is `3/2`,
   proves `3/8<=log(3/2)` without new mathematical assumptions.
2. Hence the unchanged beta0 `log(3/2)/64>=3/512`.
3. Pinned Mathlib `Real.log_two_lt_d9` gives `log 4 < 139/100`.
4. The exact original plaquette count
   `p_H=24*(H+1)^3>=81000` for all `H>=14`.
5. Combining positivity and exact rational inequalities gives
   ```text
   H>=14 ==>
   beta0²*p_H/2 >= 81000*(3/512)²/2
               = 91125/65536 > 139/100 > log 4.
   ```
6. With AKO's independently already-certified `H<=13` direction,
   the complete sharp criterion equivalence is
   ```text
   beta0²*p_H/2 <= log 4  <->  H <= 13.
   ```

The theorem is about the precise **AKN scalar sufficient no-witness
criterion**, not about actual AJA finite-power witness existence at H>=14.
Treat the latter as an unfilled obstruction (NO_DATA).

## Exact-source, independent receipts and canonical merge

[AKP theorem PR #6694](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6694).
Exact source HEAD `e3701e9a92831c5dcb788c9a0562c7b321277401`.
[Exact-source CI #43197769130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43197769130)
completed **SUCCESS**: **11,452/11,452** changed-Lean dependency
closure, all **6/6** new declarations' individual `#print axioms`
show exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
changed AKP warning/error **0/0**, independent completion receipt
completed/SUCCESS with exact-head commit status success.

Theorem PR was **MERGED** into canonical formal at
`7ca307b8183663e66a8cc1d70b6b8ef5756bcb31`.
Source, actual test-merge, and squash Git trees are identical:
`3bfa897c75cc512ae2f46f75b32e8b212a632d5f`.
Independent formal-push [CI #43198677404](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43198677404)
has a separate exact integrated-source verification, not conflated
with the original PR-source receipt.

No original physical definitions, existing imported source code,
assumptions, root, Lean version `v4.30.0-rc2`,
mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
or CI workflow changed. Only a new Lean leaf was added.
Append-only / tighten-only / overwrite-forbidden / same-root.

## OPEN: original Haar/top comparison beyond quadratic sufficient criterion

At fixed beta0 and H>=14, this scalar criterion does not apply:
`beta0²*p_H/2 > log 4`. This is **not** the impossibility
of an AJA witness and is **not** a proof of a witness. A separate
comparison of the genuine original negative-region Haar budget with
the full-top energy is required before drawing any result.

The original GL-source H-uniform Rayleigh bound, Hamiltonian
spectral gap and 4D continuum Yang--Mills mass gap remain outside
the verified scope. Formal contains the theorem and this record;
main mirrors only the identical record blob and public appendices.
Docs-only Strict Lean is not manually dispatched.
