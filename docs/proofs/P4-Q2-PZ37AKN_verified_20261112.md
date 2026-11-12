# P4-Q2-PZ37AKN — original halfweighted top/Haar quadratic no-witness (2026-11-12 JST)

## Scope and retained genuine definitions

Canonical theorem repository: `itakura-hidetoshi/4d-mass-gap`, canonical formal branch `formal/real-hilbert-uniform-coercive-strong-limit`. This leaf adds **no replacement** of the finite spatial H SU(2) Wilson physical one-slab transfer `P`, normalized `S=P/||P||`, original signed centered ZW source `f0`, full S-fixed top projection `Q`, Haar probability `mu_H`, genuine spatial halfweight `w`, normalized source `u`, original negative margin `m`, or original negative region. The genuine original AJA budget remains

```text
B_(H,beta) = m_(H,beta)^2 * Measure.real mu_H
  {U | u_(H,beta)(U) < -m_(H,beta)}.
AJA witness: exists n : Nat, ||(S_(H,beta)^n) f0_H||² < B_(H,beta).
```

The result is a **no-go for this sufficient-test witness**, not a failure of the general Yang–Mills mass-gap conjecture.

## Fourteen kernel-certified declarations

One new 537-line Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHalfWeightedTopQuadraticAJANoGoV5_PZ37AKN.lean`.

Five general analytical facts prove bounded-halfweight L1 integrability, a genuinely weighted kernel L2 pairing bound, pairing with a nonnegative eigenfunction, the scaled overlap estimate, and the exact original margin comparison. Nine original-model facts apply them to the unchanged finite-volume Wilson definitions. Every declaration has its own `#print axioms`.

For beta>0, write:
```text
a = beta * exp(-2*beta*p_H)*V_H
lambda = ||P_(H,beta)|| > 0
psi = actual unit nonnegative physical top eigenvector
J = integral w_(H,beta) * psi dmu_H
F = inner(f0_H,psi) <= 0
Z = actual crossing partition Z_H(beta)
```

The original halfweight is preserved on both endpoints of the kernel bound, yielding `lambda <= J²`. The true weighted Ward affine estimate gives `(lambda-c)*F <= -a*J`, with `c>=0`, hence `a²<=lambda*F²`. The **unchanged original margin identity** is `m*lambda=a*Z/2`. Genuine AIQ Gaussian comparison plus original AIW norm lower bound yields:
```text
beta² * p_H / 2 <= log 4  ==>  Z² <= 4*lambda.
```

Since the Haar negative-region measure is at most one, for every n : Nat:
```text
beta > 0 and beta²*p_H/2 <= log 4 ==>
B_original(H,beta) <= m² <= F²
  <= ||Q f0_H||² <= ||S_(H,beta)^n f0_H||².
```
Therefore **no strict genuine original AJA finite-power witness exists** under the stated scalar quadratic condition. This is a direct *reverse* top/Haar budget comparison; neither `||Qf0||²<B` nor any other top-smallness assumption has been added.

At unchanged `beta0=log(3/2)/64`, `beta0<=1/128`; for every original `H<=10` the exact plaquette count satisfies `p_H<=31944`, and
```text
beta0²*p_H/2 <= 31944/(2*128²) = 3993/4096 < 1 <= log 4.
```
Consequently the no-witness theorem holds **for all H<=10**, including H=1 beyond the earlier explicit fixed-coupling H=0 obstruction. No assertion is made for arbitrary H>10 or positive beta outside the certified scalar region.

## Exact-source verification and repairs

[Theorem PR #6688](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6688) was initially closed as unverified after [failed CI #43187400636](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43187400636), whose kernel log reported pointwise `norm_mul`, `integral_prod_mul` application, positivity, local `muN.prod` notation and field-normalization failures. Original failed elaborations' `sorryAx` dependencies were **not** accepted as a proof.

Reopened draft PR and patched **the existing new leaf only**:
- `bc2dc7b1eb732d4224606d6a1fa580ec24ff15bb`: explicit pointwise application for norms, explicit product integral parameters and functions, original positive plaquette-count fact, parentheses on the local Haar measure notation, and removal of an unreachable tactic.
- [failed CI #43190075054](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43190075054) exposed two remaining proof-script elaboration issues; these were inspected in the full dependency-log context.
- `94edaf7576001dda0237e488217f6ab8798efcb9`: use definitional original margin equality directly and simplify the `Nat` exponent cast after `Real.log_pow`.

[Final exact-source CI #43191093628](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43191093628) at exact source SHA `94edaf7576001dda0237e488217f6ab8798efcb9`: completed/**SUCCESS**, changed Lean dependency closure **11,450/11,450**, 14/14 new theorem axiom audits exactly the standard three `[propext, Classical.choice, Quot.sound]`, new `sorryAx` absent, AKN warning/error **0/0**. Independent completion receipt job also completed/SUCCESS and exact-source commit-status receipt was `success`.

PR #6688 was **MERGED** by squash into the canonical formal branch at `ca23a8d07c522e3a9e893d814936275619bc085d`. Exact-source, actual synthetic test merge, and canonical squash Git tree are **identical**:
`9206ca6befa39921a31e0e7bfd0fc9d93cb0ecb6`.
Separate post-merge formal push [CI #43192002019](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43192002019) is separately assessed below once completed; no CI is deemed verified while pending.

## Relationship to certified AKL/AKM and remaining obstruction

AKL uniform top-orthogonal contraction and AKM true orbit envelope
`L_AKK<=||Qf0||²<=||S^n f0||²<=||Qf0||²+(3071/3072)^(2*n)*||Q^perp f0||²`
do **not** themselves imply an original AJA witness. AKN now certifies the opposite comparison `B_original<=||Qf0||²` on a genuine explicit quadratic coupling region. These results are compatible and preserve the physical normalization and the top projection.

OPEN/NO_DATA: fixed beta0 and H>10 outside the certified scalar regime; unqualified top-vs-Haar comparison for all H and beta; whether fixed beta0 lies in AKL's H-independent coercivity cutoff; a common finite-power AJA witness; original GL/Rayleigh lower bound, Hamiltonian gap and continuum 4D Yang–Mills mass gap. No new global gap claim follows.

Provenance: append-only / tighten-only / overwrite-forbidden / same-root; fixed Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No changes to existing physical files, root, pinned dependency or workflow. Documentation-only Strict Lean must not be manually dispatched.
