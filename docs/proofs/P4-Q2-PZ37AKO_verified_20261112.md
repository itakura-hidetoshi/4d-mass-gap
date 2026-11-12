# P4-Q2-PZ37AKO — original fixed beta0 genuine AJA quadratic no-witness through H=13

Date: 2026-11-12 JST. Canonical theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Exact unchanged physical model and scope

Keep the original finite-H SU(2) Wilson physical transfer `P_(H,beta)`,
normalized `S=P/||P||`, centered signed ZW source `f0_H`, original
spatial halfweight, Haar probability, top projection Q, normalized source
`u_(H,beta)`, original normalized negative margin `m_(H,beta)`, and original
negative-region budget

```text
B_(H,beta) = m_(H,beta)^2 *
  Measure.real mu_H {U | u_(H,beta)(U) < -m_(H,beta)}.
```

The prior AKN kernel-certified theorem, without changes to source, operator,
region or budget, states that for positive beta satisfying
`beta^2 * p_H / 2 <= log 4`, the actual source orbit obeys
`B_original <= ||Q f0_H||² <= ||S_(H,beta)^n f0_H||²` for **every n : Nat**.
Thus the strict original finite-power AJA witness is absent on that region.

## Seven new kernel-verified declarations

One new Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticAJANoGoThroughThirteenV5_PZ37AKO.lean`.

The theorem chain does not introduce a smaller substitute coupling or a
top-smallness premise:

1. Rational inequality `(3/2 : R) <= (79/78)^32` and pinned Mathlib
   `Real.log_le_log`, `Real.log_pow`, `Real.log_le_sub_one_of_pos` yield
   `log(3/2) <= 16/39`.
2. Hence the **unchanged original** beta0 `log(3/2)/64 <= 1/156`.
3. The existing fixed pinned Mathlib theorem `Real.log_two_gt_d9`,
   together with `log(4)=2*log(2)`, proves `11/8 <= log 4`.
4. The exact original plaquette count
   `p_H = 24*(H+1)^3 <= 65856` holds for every `H<=13`.
5. By positivity and squaring:
   ```text
   beta0² * p_H / 2 <= 65856/(2*156²) = 686/507
                       < 11/8 <= log 4.
   ```
6. Apply AKN's **genuine original** quadratic no-witness theorem to prove
   for every `H<=13`: no `n : Nat` with `||S^n f0_H||² < B_(H,beta0)`.
7. Specialize to `H=13` with its exact unmodified physical L² carrier.

This strictly extends the previously certified AK N original fixed-coupling
`H<=10` statement to `H=11,12,13`. The result concerns the sufficient
strict AJA Haar budget and **does not refute or prove** the 4D Yang--Mills mass gap.

## Lean4 exact-source verification and provenance

[AKO theorem PR #6691](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6691),
original head `d000ea9856c8a6039532aac30d04ead02c2a29fc`.
[Exact-source CI #43195520536](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43195520536)
completed **SUCCESS**: full dependency closure **11,451/11,451**, 7/7
mathematical declarations audited with individual `#print axioms`,
each exactly `[propext, Classical.choice, Quot.sound]`. No new `sorryAx`,
modified AKO warning/error **0/0**, exact-head independent completion receipt
completed/SUCCESS, commit status `success`.

Theorem squash **MERGED** at canonical formal
`06a9f3448894f1b3f3311660949e74fc98f382b6`.
Certified source, actual synthetic test merge, and canonical squash share
Git tree `f5c79a356e8f734cc0255316247d7477c7742601` (identity checked).
Separate post-merge formal push
[CI #43196476342](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43196476342)
is independently audited and not conflated with the source CI.

All original physical definitions, imports of existing leaves, root,
Lean v4.30.0-rc2, mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, and workflows remain
unchanged. Append-only / tighten-only / overwrite-forbidden / same-root.

## Remaining obstruction

At fixed beta0 and H>=14 the present source proof provides **NO_DATA**
about the strict AJA witness. Failure to establish the *sufficient*
quadratic criterion does not mean a witness exists. Whether a new direct
genuine Haar/top comparison can determine the result beyond this region
is an independent research question. No H-uniform original GL-source
Rayleigh lower bound, Hamiltonian gap or continuum Yang--Mills mass gap is
claimed.

Formal theorem source and proof record are canonical. Main receives only
the exact matching proof record blob and appended public-document notes;
docs-only Strict Lean is not manually dispatched.
