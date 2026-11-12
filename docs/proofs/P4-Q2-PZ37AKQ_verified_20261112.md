# P4-Q2-PZ37AKQ — original H=14 Haar-negative mass-sensitive AJA comparison

Date: 2026-11-12 JST. Canonical theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## What is proven, and what remains unobserved

Keep EXACT original SU(2) Wilson one-slab physical P, normalized
S=P/||P||, signed centered ZW source f0, true full-top eigenspace
projection Q, Haar measure mu_H, original spatial halfweight w,
normalized source u, original negative margin m, and original AJA
Haar-budget B=m^2 mu_H{U:u(U)<-m}.

The earlier certified AKP exact scalar condition holds at fixed beta0
iff H<=13. Its failure at H=14 does **not** assert an AJA witness.
AKQ retains the actual original negative-region Haar mass r rather
than replacing it with the probability bound one.

Let lambda=||P_(H,beta)||>0, Z=the original crossing partition,
F=<f0,psi> for the genuine nonnegative top eigenvector, and
a=beta exp(-2beta p_H) V_H. AKN's actual weighted-Ward overlap
`a^2<=lambda*F^2`, the original exact margin
`m*lambda=a*Z/2`, and full-top projection give

```text
r * Z² <= 4*lambda  ==>
B = m²*r <= F² <= ||Q f0||² <= ||S^n f0||² for every n:Nat.
```

This is a new genuine Haar-mass-sensitive **sufficient no-witness**
test, not a theorem that the test is automatically satisfied.

The original AIW spatial-mean norm floor `exp(-beta*p_H)*Z<=lambda`
and original AIQ Gaussian crossing bound
`Z<=exp(-beta*p_H)*exp(beta²*p_H/2)` reduce it further to

```text
r*exp(beta²*p_H/2) <= 4  ==>  no strict original AJA witness.
```

At H=14 and original beta0=log(3/2)/64, the exact original p_14=81000.
The sufficient condition becomes

```text
r_14*exp(beta0²*81000/2) <= 4.
Equivalently r_14 <= 4*exp(-beta0²*81000/2).
```

The right side is approximately `0.787208553359`. This decimal
is an ordinary numerical interpretation of an exact analytic
threshold, **not** a certified or measured Haar mass. A finite-power
witness, if separately proved, would require the strict reverse
inequality `4 < r_14*exp(beta0²*81000/2)`.
Neither direction is certified for the actual r_14.

The original full-top/budget equivalence remains independently
certified in AJI: at beta0 and finite H=14,
`exists n>=1, ||S^n f0||²<B iff ||Qf0||²<B`.
AKQ does **not** substitute the top projection with the single
positive eigenvector; that vector provides only a lower bound.

## Kernel-certified seven declarations and provenance

One new 318-line Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH14WeightedHaarMassThresholdV5_PZ37AKQ.lean`.
Seven declarations comprise a real-algebraic weighted margin-budget
inequality; the original physical budget-to-top implication;
an all-powers genuine no-witness; exact-partition and
Gaussian-partition Haar-mass sufficient tests; H14 specialization;
and the necessary strict Haar-mass condition for any witness.

[AKQ theorem PR #6696](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6696)
merged to canonical formal as
`517ed6be3b9032c9d6c01fc52ec9432fa924f7da`.
Exact source HEAD `24ac9f2d5e720c2dabfbc9884b8065bad3d03eef`.
[Exact-source CI #43203431326](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43203431326)
completed **SUCCESS**: changed-Lean dependency closure
**11,453/11,453**, all 7/7 individual `#print axioms`
strictly `[propext, Classical.choice, Quot.sound]`, no new
`sorryAx`, AKQ warning/error **0/0**, independent exact-head
completion receipt completed/SUCCESS and commit status success.

Source HEAD, tested synthetic test merge, and canonical squash
share the same Git tree
`33dc7aaa323ce4948b8c8cbb224b5f11413f253c`.
The independent formal-branch push
[CI #43204266634](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43204266634)
must be checked separately before recording its SUCCESS.

No original definitions, imported theorem signatures, Lean/mathlib
pinned versions, root or workflow changed. One new Lean leaf only.
append-only / tighten-only / overwrite-forbidden / same-root.

## NEXT: quantitative actual original Haar certification

The exact original H14 negative-region mass upper bound is **NO_DATA**.
A valid continuation is to construct a finite, rigorously
verified cover of the actual set `{u_14<-m_14}` by measurable
cells with total original Haar mass at most the exact threshold,
or separately certify its complement mass at least
`1-4*exp(-beta0²*81000/2)`. A floating-point Monte Carlo
estimate, a redefined source/region or a local-cell observation
alone cannot certify the global comparison.

The true full-top energy comparison may also be evaluated
directly by original signed-Haar certificates. No unconditional
H14 witness or no-witness, H-uniform source Rayleigh,
Hamiltonian or continuum 4D Yang--Mills mass gap is claimed.
Formal is the theorem canonical branch; main mirrors only exact
proof-record blob and appended public documentation. Docs-only
Strict Lean is not manually dispatched.

## Independent canonical formal-squash push verification — 2026-11-12 JST

The separately triggered actual canonical squash `push`
[CI #43204266634](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43204266634)
at integrated SHA `517ed6be3b9032c9d6c01fc52ec9432fa924f7da`
completed **SUCCESS**, with independent Lean job `131135320208`
and exact-head receipt job `131138679934` both completed/SUCCESS.
The full job log has `[11453/11453] Built ...PZ37AKQ`, all 7/7
multiline axiom prints only `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`, modified AKQ warning/error **0/0**. The separate
receipt shows `event=push`, the exact integrated SHA,
`source_result=success` and published status `success`.

This independently authenticates the original-model theorem squash tree
`33dc7aaa323ce4948b8c8cbb224b5f11413f253c`,
not the unknown actual H14 Haar mass. The mathematical statement remains
a **conditional no-witness criterion** and a necessary mass condition
for any hypothesized strict original finite-power AJA witness.
