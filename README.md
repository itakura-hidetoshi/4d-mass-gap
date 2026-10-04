# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PR #5112

The finite-volume positive-coupling transfer-gap route remains closed with the explicit volume/rank/scale-uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The q0 estimate is available on the full completed physical pair non-top sector.

The old completed H1-D5 cross-scale compatibility is formally refuted at positive SU(2) coupling and must not be reintroduced under another name.

The active continuum-existence route is now much weaker.  The evolved three-mode problem has been reduced from whole selected-marginal operator compatibility to a finite adjacent-refinement problem, and then further to vector-wise mismatch only along the finite Krylov orbit.

The current model-facing H1-C3 frontier is

~~~text
orbit-wise cross-volume refinement geometry
  +
same-fine-volume Wilson coupling response.
~~~

The coupling side is now close to explicit actual-model control:

- #5109: exact one-slab Wilson kernel is beta-Lipschitz;
- #5110: the estimate is lifted to the ordered-pair kernel, product-L2 kernel, and raw pair-transfer operator;
- #5111: the physical one-slab normalization denominator has an explicit Wilson minorization-floor lower bound, including inverse-square control;
- #5112: the physical one-slab transfer and its norm are beta-Lipschitz.

The immediate next theorem is to combine #5110/#5111/#5112 into an explicit bound for the **normalized physical pair-transfer coupling residual** that appears in #5108.

A complete four-dimensional continuum Yang--Mills existence theorem, physical-time Hamiltonian construction, and Wightman mass-gap theorem are **not yet claimed**.

---

## Authority checkpoint — 2026-10-04 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline before this docs refresh | `456825cf29e913d6a5fcd3879e59aec08f16ac9e` |
| #5111 | explicit global-minorization lower bound for physical transfer normalization |
| #5111 exact head | `3adc831bcc48cdf521f6b20291953109cf82b1de` |
| #5111 Lean Fast Check | run `37187331576` — success |
| #5111 exact-head receipt | success |
| #5112 | beta-Lipschitz control of physical one-slab transfer and its norm |
| #5112 exact head | `ae653b561c467a762fd05be118ff8d1ba20e5e33` |
| #5112 Lean Fast Check | run `37187333520` — success |
| #5112 exact-head receipt | success |
| Pinned Lean | `v4.30.0-rc2` |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

The GitHub default branch `main` is not theorem authority.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

README / ROADMAP-only commits are docs-only and do not replace the latest theorem-bearing baseline.

---

## 1. Closed finite-volume quantitative route

Already formalized:

- beta = 0 physical transfer gap = 1;
- positive-beta finite-volume coercivity;
- explicit scale/rank/volume-uniform lower gap floor;
- one-dimensional finite physical top eigenspace;
- one-dimensional completed pair top-top sector;
- full completed physical pair non-top receiver;
- uniform
  `q0 = 3071/3072 < 1`;
- natural-time power decay
  `||R_n^m x|| <= q0^m ||x||`.

This is a reusable receiver.  It is no longer the active bottleneck.

---

## 2. H1-D4 closed; completed H1-D5 closed as a no-go

The repository proves

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

So independent endpoint gauge-fixedness is no longer an assumption.

By contrast, the old completed H1-D5 compatibility is too strong.  The formal chain forces a rank-one normalized one-slab transfer, while the explicit positive-coupling SU(2) two-mode sector proves a nondegenerate opposite statement.

Therefore

~~~text
beta(n) > 0
  ->
not completed H1-D5 at scale n.
~~~

Do not reintroduce:

- completed H1-D5;
- vacuum/top alignment;
- rank-one forcing;
- OS-boundary transfer = physical pair transfer by fiat;
- a renamed equivalent cross-scale operator compatibility assumption.

---

## 3. Three-mode SU(2) finite excitation route — closed kinematics

The repository has theorem-generated SU(2) Wilson-energy Gram--Schmidt modes with:

- explicit finite Wilson observables;
- gauge-invariant physical one-slice representatives;
- physical ordered endpoint-pair representatives;
- membership in the completed physical pair carrier;
- orthonormality of the pair family.

The first three modes define an exact finite synthesis

~~~text
A_{n,0} : R^3 -> finite physical pair Hilbert space.
~~~

A two-functional rank-nullity selector produces a unit coefficient vector satisfying both:

~~~text
vacuum pairing = 0
pair-top pairing = 0.
~~~

Thus the finite selected excitation is norm one, nonzero, and exactly non-top before taking a limit.

This avoids the old vacuum/top-fidelity seam.

---

## 4. #5090--#5097: evolved strong limits reduced to finite Cauchy data

The dynamical existence problem was successively weakened.

### #5090

Whole selected-marginal operator compatibility was replaced by pointwise strong coherence of the evolved three-mode synthesis

~~~text
A_{n,m} : R^3 -> L2_cont.
~~~

### #5091

It is enough to control the three standard basis Krylov vectors.

### #5092

Each vector convergence is reduced to scalar norm/inner-product convergence.

### #5093

Finite norm-squared is rewritten as the concrete 2m-step self-correlation

~~~text
||S_n^m u_{n,k}||^2
  =
<S_n^(2m) u_{n,k}, u_{n,k}>.
~~~

### #5094

The continuum candidate vector is eliminated.  Finite pair correlations give Cauchy control, and completeness theorem-generates the continuum vector.

### #5095

Cross-scale continuum inner products are eliminated by transporting both scales to one finite union marginal.

### #5096

The whole tail comparison is reduced to the finite common-marginal Cauchy defect

~~~text
d_{n,j}^{m,k}
  =
||x~_{n,m,k} - x~_{j,m,k}||.
~~~

### #5097

At time zero the theorem-generated continuum three-mode synthesis is a genuine linear isometry:

~~~text
||A_{infty,0} c|| = ||c||.
~~~

Hence a unit coefficient vector produces a norm-one, nonzero continuum initial excitation once the Cauchy route is available.

---

## 5. #5098--#5103: all-tail control reduced to adjacent transfer mismatch

### #5098

Mathlib's `cauchySeq_of_summable_dist` reduces all-tail Cauchy control to summability of adjacent defects:

~~~text
sum_n d_n^{m,k} < infinity.
~~~

### #5099

A geometric adjacent bound

~~~text
d_n^{m,k} <= C_{m,k} q_{m,k}^n
0 <= q_{m,k} < 1
~~~

is sufficient.

### #5100

For contractions:

~~~text
||A^m x - B^m y||
  <=
||x-y|| + m ||A-B||.
~~~

### #5101

The time-zero adjacent defect is eventually exactly zero under the existing coherent readout, hence summable.

### #5102

Consecutive scales are placed on one finite union-marginal Hilbert space with common-marginal transfers

~~~text
A_n^L
A_n^R
~~~

satisfying

~~~text
||A_n^L|| <= 1
||A_n^R|| <= 1
~~~

and exact Krylov-power intertwining.

### #5103

The evolved adjacent defect obeys

~~~text
d_n^{m,k}
  <=
d_n^{0,k}
  +
m ||A_n^L - A_n^R||.
~~~

Thus summable common-transfer mismatch is enough for every fixed natural time.

---

## 6. #5104--#5108: full operator mismatch weakened to Krylov-orbit mismatch

### #5104

Geometric full operator mismatch

~~~text
||A_n^L - A_n^R|| <= C q^n
q < 1
~~~

implies all fixed-time strong limits and preserves the existing q0^m decay.

This is a valid sufficient route, but it is stronger than necessary.

### #5105

The whole-space mismatch is split into

~~~text
cross-volume geometry residual
  +
same-fine-volume coupling residual.
~~~

### #5106

A sharper telescoping theorem removes the need for whole-space operator-norm convergence:

~~~text
||A^m x - B^m y||
  <=
||x-y||
  +
sum_{r < m} ||(A-B)(B^r y)||.
~~~

For the actual adjacent SU(2) problem, it is enough to control

~~~text
e_{n,r,k}
  =
||(A_n^L - A_n^R) (A_n^R)^r v_{n,k}^R||
~~~

for each fixed finite orbit depth r and mode k.

### #5107

If for every fixed r,k

~~~text
e_{n,r,k} <= C_{r,k} q_{r,k}^n
0 <= q_{r,k} < 1,
~~~

then all fixed-natural-time strong limits follow.

### #5108

The orbit mismatch is split further:

~~~text
e_{n,r,k}
  <=
g_{n,r,k} + c_n,
~~~

where

~~~text
g_{n,r,k}
  = orbit-wise cross-volume geometry/refinement residual,

c_n
  = same-fine-volume normalized physical pair-transfer coupling residual.
~~~

Therefore the present H1-C3 model-facing task no longer requires full cross-volume operator-norm convergence.

---

## 7. #5109--#5112: actual finite Wilson control of the coupling side

This is the newest theorem-bearing layer.

### #5109 — exact one-slab Wilson kernel beta-Lipschitz

The exact one-slab kernel is

~~~text
K_beta(A,B) = exp(- beta * S_slab(A,B)).
~~~

Using the nonnegative slab action and the explicit finite global action budget `B_H`:

~~~text
||K_gamma(A,B) - K_beta(A,B)||
  <=
B_H ||gamma - beta||.
~~~

No gap or cross-scale compatibility assumption enters.

### #5110 — lift beta response to pair transfer

The ordered-pair kernel is a product of two one-slab kernels.

The repository proves

~~~text
||K2_gamma - K2_beta||
  <=
2 B_H ||gamma - beta||
~~~

pointwise, then with the same coefficient in product-Haar L2, and finally for the raw ambient pair-transfer operator norm.

It also adds the square Hilbert--Schmidt kernel-operator 1-Lipschitz API.

### #5111 — explicit normalization denominator floor

Let

~~~text
m_H(beta)
  =
exp(- beta * globalActionBudget(H)).
~~~

Then

~~~text
m_H(beta)
  <=
<T_phys 1, 1>
  <=
||T_phys||.
~~~

Consequently:

~~~text
||T_phys||^(-1)
  <=
m_H(beta)^(-1),

(||T_phys||^2)^(-1)
  <=
(m_H(beta)^2)^(-1).
~~~

So the normalization denominator is no longer controlled merely by positivity; it has an explicit finite Wilson lower certificate.

### #5112 — physical transfer beta-Lipschitz

The one-slab kernel estimate is lifted through product-Haar L2, Hilbert--Schmidt transfer, and the Gauss-law physical restriction.

The repository now has

~~~text
||T_phys(gamma) - T_phys(beta)||
  <=
B_H ||gamma - beta||
~~~

and therefore

~~~text
|||T_phys(gamma)|| - ||T_phys(beta)|||
  <=
B_H ||gamma - beta||.
~~~

This is the missing numerator for explicit variation of the inverse-square normalization coefficient.

---

## 8. Immediate current theorem target

The next theorem should combine #5110, #5111 and #5112 for the normalized physical pair transfer.

Schematically, if

~~~text
P_beta
  = raw physical pair transfer,

a_beta
  = ||T_phys(beta)||^(-2),

S_beta
  = a_beta P_beta,
~~~

then use

~~~text
S_gamma - S_beta
  =
a_gamma (P_gamma - P_beta)
  +
(a_gamma - a_beta) P_beta.
~~~

Already available:

~~~text
raw pair-transfer beta variation            #5110
explicit lower bounds for a_beta denominator #5111
physical transfer norm variation             #5112
finite transfer norm/contraction bounds       existing
~~~

Target output:

~~~text
||S_gamma - S_beta||
  <=
explicit finite-volume coefficient(H,beta,gamma)
  * ||gamma - beta||.
~~~

Specialize to

~~~text
H = halfExtent(n+1)
beta = beta(n)
gamma = beta(n+1)
~~~

to obtain an explicit bound for the #5108 coupling residual `c_n`.

Then summability or geometric decay of that explicit coefficient-weighted beta increment closes the coupling half of #5108.

---

## 9. Remaining H1-C3 obstruction after the coupling side

Even after the normalized coupling residual is bounded explicitly, the genuinely cross-volume term remains:

~~~text
g_{n,r,k}
  =
orbit-wise geometry/refinement residual.
~~~

This is now the sharpest H1-C3 geometry frontier.

It is substantially weaker than:

- exact cross-scale transfer compatibility;
- full selected-marginal operator convergence;
- full common-transfer operator-norm convergence.

The target is only the action of the frozen-coupling coarse/fine transfer difference on finitely many actual Krylov-orbit vectors.

---

## 10. What is conditionally closed versus actual-model closed

### Actual-model closed

- finite q0 receiver;
- nonzero norm-one time-zero excitation mechanism;
- adjacent common-marginal representation;
- time-zero adjacent defect eventual zero;
- exact one-slab Wilson beta response;
- raw pair-transfer beta response;
- explicit normalization floor;
- physical one-slab transfer norm beta response.

### Closed as functional-analytic implication

If either

~~~text
sum_n e_{n,r,k} < infinity
~~~

for all fixed r,k, or a geometric majorant holds, then all fixed-natural-time evolved strong limits exist and inherit the q0^m bound.

### Not yet actual-model closed

- summability/geometric decay of orbit-wise geometry residual `g_{n,r,k}`;
- explicit final bound and summability for normalized coupling residual `c_n`;
- identification of one limiting discrete-time transfer operator on a continuum excitation subspace;
- spacing-scaled physical-time dynamics.

---

## 11. H2 — physical-time scaling remains separate

The fixed natural-time factor

~~~text
q0 = 3071/3072
~~~

is not itself a continuum physical mass.

If lattice spacing `a_n -> 0`, then naively

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed `t > 0`.

That is instantaneous collapse, not a nontrivial strongly continuous physical-time semigroup.

The physical-time layer needs scale-sensitive data such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent rescaled generator / Dirichlet / Poincare estimate.

H2 must not be conflated with the fixed-natural-time H1-C3 strong-limit problem.

---

## 12. H3/H4 — OS Hamiltonian and Wightman mass gap

After H1-C3 and H2 provide actual continuum dynamics, the intended route is

~~~text
continuum physical Hilbert space
  ->
strongly continuous contraction semigroup
  ->
self-adjoint OS Hamiltonian
  ->
vacuum-orthogonal spectral lower bound
  ->
positive physical mass
  ->
Wightman / energy-momentum mass gap.
~~~

Generic functional-analytic infrastructure is already extensive.

The missing work is model-facing identification and scaling.

---

## 13. Lean / CI engineering rules

Repository rules to preserve:

- fresh exact theorem-carrier SHA has highest authority;
- pinned Lean `v4.30.0-rc2` and pinned mathlib APIs are authoritative;
- inspect the whole changed Lean file, not only the first compiler error;
- separate mathematical failures from coercion/elaboration/typeclass failures;
- theorem-bearing PRs require exact-head Lean Fast Check success;
- theorem-bearing PRs require a matching exact-head receipt;
- do not rerun strict Lean for an unchanged already-GREEN exact head;
- docs-only changes do not require a redundant strict-Lean build.

Lean 4 engineering lessons repeatedly confirmed in the #5100--#5112 series:

- section variables absent from the theorem statement are pruned from the generated signature;
- pass dependent parameters explicitly when inference is fragile;
- do not ask `simpa` to unfold huge dependent `ContinuousLinearMap` expressions;
- prefer `change` to a scalar/order goal followed by an exact theorem;
- fully apply `ContinuousLinearMap.opNorm_le_bound` rather than forcing Lean to infer the operator;
- avoid `norm_nonneg _` when the underscore requires reconstructing a huge operator type; reuse an existing positivity theorem instead;
- use the actual orientation of `add_le_add_left/right` in the pinned API;
- avoid heartbeat increases when a smaller proof term removes the elaboration obstruction.

---

## 14. Recent milestone ledger

| PR | Status | Main result |
| --- | --- | --- |
| #5090 | merged | evolved three-mode synthesis coherence suffices |
| #5091 | merged | reduce to three Krylov basis limits |
| #5092 | merged | reduce strong convergence to scalar convergence |
| #5093 | merged | finite norm² = 2m-step self-correlation |
| #5094 | merged | candidate-free Cauchy construction |
| #5095 | merged | cross-scale pair correlations moved to finite union marginals |
| #5096 | merged | finite common-marginal Cauchy defect frontier |
| #5097 | merged | time-zero continuum synthesis isometry |
| #5098 | merged | summable adjacent defects imply Cauchy |
| #5099 | merged | geometric adjacent defect majorant |
| #5100 | merged | contraction-power perturbation theorem |
| #5101 | merged | time-zero adjacent defect eventually zero |
| #5102 | merged | adjacent transfers on one common finite marginal |
| #5103 | merged | `d_m <= d_0 + m ||A_L-A_R||` |
| #5104 | merged | geometric common-transfer mismatch -> strong limits |
| #5105 | merged | whole-space mismatch = geometry + coupling bound |
| #5106 | merged | reduce to finite Krylov-orbit mismatch |
| #5107 | merged | geometric orbit mismatch -> strong limits |
| #5108 | merged | orbit mismatch <= orbit geometry + coupling |
| #5109 | merged | exact one-slab kernel beta-Lipschitz |
| #5110 | merged | pair kernel/L2/raw pair transfer beta-Lipschitz |
| #5111 | merged | explicit physical normalization floor and inverse-square bound |
| #5112 | merged | physical transfer and transfer-norm beta-Lipschitz |

---

## 15. Restart checkpoint

Latest theorem-bearing baseline before this docs refresh:

~~~text
456825cf29e913d6a5fcd3879e59aec08f16ac9e
~~~

Read these files first:

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatch.lean` — #5106
2. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometric.lean` — #5107
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatchSplit.lean` — #5108
4. `PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz.lean` — #5109
5. `PeriodicHypercubicEvenSpecialUnitaryOneSlabPairBetaLipschitz.lean` — #5110
6. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor.lean` — #5111
7. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz.lean` — #5112
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransfer.lean` — #5102
9. `ContinuousLinearMapContractionPowerPerturbation.lean` — #5100

Current restart target:

~~~text
#5110 raw pair-transfer beta response
  +
#5111 explicit normalization denominator floor
  +
#5112 physical transfer-norm beta response
  ->
explicit normalized physical pair-transfer beta perturbation bound
  ->
explicit #5108 coupling residual c_n
  ->
summability / geometric beta-increment criterion

IN PARALLEL / NEXT:
  orbit-wise cross-volume geometry residual g_{n,r,k}
  ->
summability or geometric refinement estimate

THEN:
  #5108
  ->
#5106/#5107
  ->
all fixed-natural-time evolved strong limits
  ->
continuum discrete-time q0 receiver

THEN:
  physical-time scaling (H2)

LATER:
  OS Hamiltonian
  ->
spectral / Wightman mass gap.
~~~
