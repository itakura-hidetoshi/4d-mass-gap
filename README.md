# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PR #5124

The finite-volume positive-coupling transfer-gap route remains closed with the explicit volume/rank/scale-uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The q0 estimate is available on the full completed physical pair non-top sector.

The old completed H1-D5 cross-scale compatibility is formally refuted at positive SU(2) coupling and must not be reintroduced under another name.

The active continuum-existence route has now been weakened much further than the old whole-operator formulation.  The evolved three-mode problem is reduced to adjacent finite-volume vector-wise data along fixed finite Krylov orbits.  The coupling part is explicit.  The remaining geometry has been rewritten through one canonical fine-to-coarse reconstruction and, for its projective part, one common-marginal orthogonal-projection variance defect.

The present model-facing H1-C3 frontier is therefore

~~~text
finite physical transfer/reconstruction commutation
  +
common-marginal coarse-physical projection variance tail
  +
explicit beta-increment majorant.
~~~

The second term is now exactly

~~~text
V_{n,r,k}
  =
||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2,
~~~

where (Y_{n,r,k}) is the frozen-coupling fine output embedded into the adjacent common finite marginal and (P_n^{phys}) is the orthogonal projection onto the coarse embedded completed physical pair carrier.

This is the direct interface to the repository's existing self-adjoint/idempotent conditional-expectation and finite-influence machinery.

A complete four-dimensional continuum Yang--Mills existence theorem, a nontrivial physical-time Hamiltonian, and a Wightman / energy-momentum mass-gap theorem are **not yet claimed**.

---

## Authority checkpoint — 2026-10-04 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Current theorem-carrier SHA before this docs refresh | `28a58a37f2cb1da525a670e05bbece16867f3809` |
| Latest theorem-bearing baseline before this docs refresh | `28a58a37f2cb1da525a670e05bbece16867f3809` |
| Latest theorem-bearing PR | #5124 |
| #5124 exact head | `7dd08ccad353fbf4dd13249584e287673849616a` |
| #5124 Lean Fast Check | run `37201727923` — success |
| #5124 exact-head receipt | success |
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
- a renamed equivalent cross-scale whole-operator compatibility assumption.

---

## 3. Three-mode SU(2) finite excitation route — closed kinematics

The repository theorem-generates SU(2) Wilson-energy Gram--Schmidt modes with:

- explicit finite Wilson observables;
- gauge-invariant physical one-slice representatives;
- physical ordered endpoint-pair representatives;
- membership in the completed physical pair carrier;
- orthonormality of the pair family.

The first three modes define an exact finite synthesis

~~~text
A_{n,0} : R^3 -> finite physical pair Hilbert space.
~~~

A two-functional rank-nullity selector produces a unit coefficient vector satisfying both

~~~text
vacuum pairing = 0
pair-top pairing = 0.
~~~

Thus the finite selected excitation is norm one, nonzero, and exactly non-top before taking a limit.

This avoids the old vacuum/top-fidelity seam.

---

## 4. #5090--#5097: strong-limit existence reduced to finite Cauchy data

The dynamical existence problem was successively weakened.

### #5090--#5093

The evolved three-mode problem was reduced from whole selected-marginal compatibility to three fixed Krylov-basis limits and then to scalar norm / inner-product convergence.  Finite norm-squared is rewritten as the concrete (2m)-step self-correlation

~~~text
||S_n^m u_{n,k}||^2
  =
<S_n^(2m) u_{n,k}, u_{n,k}>.
~~~

### #5094--#5096

A prechosen continuum vector is no longer required.  Finite Cauchy data theorem-generates the limit by completeness.  Cross-scale correlations are transported to one finite union marginal, leaving one common-marginal Cauchy defect.

### #5097

At time zero the theorem-generated continuum three-mode synthesis is an isometry:

~~~text
||A_{infty,0} c|| = ||c||.
~~~

Hence any unit coefficient vector gives a norm-one, nonzero continuum initial excitation once the Cauchy route closes.

---

## 5. #5098--#5108: whole-operator compatibility removed

### Adjacent summability

Mathlib's `cauchySeq_of_summable_dist` reduces all-tail Cauchy control to summability of adjacent defects.  A geometric bound (Cq^n), (0 le q < 1), is sufficient.

### Common-marginal transfer representation

Consecutive scales are placed on one finite union-marginal Hilbert space with contractions

~~~text
A_n^L
A_n^R
~~~

and exact Krylov-power intertwining.

### Orbit-wise telescoping

The key sharpening is

~~~text
||A^m x - B^m y||
  <=
||x-y||
  +
sum_{r < m} ||(A-B)(B^r y)||.
~~~

Therefore it is enough to control, for each fixed finite depth (r) and mode (k),

~~~text
e_{n,r,k}
  =
||(A_n^L - A_n^R) (A_n^R)^r v_{n,k}^R||.
~~~

No whole-space operator-norm convergence is needed.

### #5108 split

The actual orbit mismatch is bounded by

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

---

## 6. #5109--#5115: the coupling lane is explicit

### #5109 — one-slab Wilson kernel beta response

For

~~~text
K_beta(A,B) = exp(- beta * S_slab(A,B)),
~~~

the exact finite kernel satisfies

~~~text
||K_gamma(A,B) - K_beta(A,B)||
  <=
B_H ||gamma-beta||,
~~~

where (B_H) is the explicit one-slab global action budget.

### #5110 — raw ordered-pair transfer response

The estimate lifts to:

- the ordered-pair kernel;
- product-Haar (L^2);
- the raw pair-transfer operator.

In particular

~~~text
||P_gamma - P_beta||
  <=
2 B_H ||gamma-beta||.
~~~

### #5111 — explicit normalization floor

With

~~~text
m_H(beta) = exp(- beta * globalActionBudget(H)),
~~~

the repository proves

~~~text
m_H(beta) <= ||T_phys(beta)||,
~~~

hence explicit inverse and inverse-square upper bounds.

### #5112 — physical transfer norm response

~~~text
||T_phys(gamma) - T_phys(beta)||
  <=
B_H ||gamma-beta||

|||T_phys(gamma)|| - ||T_phys(beta)|||
  <=
B_H ||gamma-beta||.
~~~

### #5114 — normalized physical pair-transfer response

Writing

~~~text
S_beta = a_beta P_beta
a_beta = ||T_phys(beta)||^(-2),
~~~

the inverse-square normalization variation and the raw pair-transfer variation are combined into an explicit finite-volume operator bound

~~~text
||S_gamma - S_beta||
  <=
C_norm(H,beta,gamma) ||gamma-beta||.
~~~

### #5115 — adjacent coupling majorant

Specializing to adjacent scales gives an explicit scalar majorant

~~~text
c_n
  <=
C_norm(halfExtent(n+1), beta(n), beta(n+1))
  * ||beta(n+1)-beta(n)||.
~~~

Summability and geometric receivers are formalized.

**Conclusion:** the coupling side is no longer an abstract compatibility input.  What remains is a quantitative assumption / theorem about the chosen beta trajectory's explicit weighted increments.

---

## 7. #5116--#5119: the geometry lane is reduced to finite reconstruction

### #5116 — remove the coupling residual from the H1-C3 input

The external H1-C3 package is reduced to:

~~~text
summable orbit geometry
  +
summable explicit weighted beta increments.
~~~

The actual `c_n` is theorem-generated from #5115.

### #5117 — coarse-range projection split

The orbit-wise geometry residual is split by the canonical projection onto the coarse embedded pair-Haar range:

~~~text
g_{n,r,k}
  <=
refinement/transfer commutation residual
  +
fine-range leakage residual.
~~~

This split remains vector-wise.

### #5118 — finite-carrier representation

The actual right Krylov orbit is identified exactly as the fine pair embedding of one finite pair-Haar vector.  The two #5117 geometry pieces are rewritten as:

1. a finite coarse-carrier transfer/reconstruction mismatch;
2. the distance of one explicit fine finite vector from the coarse embedded range.

### #5119 — canonical fine-to-coarse reconstruction

A single canonical finite map is introduced:

~~~text
R_n : FinePair(n+1) -> CoarsePair(n).
~~~

Its physical version is the coarse physical-pair projection after reconstruction.

The remaining geometry becomes three finite vector-wise quantities:

1. **physical transfer/reconstruction commutation**
   ~~~text
   ||T_n R_n^phys x - R_n^phys y||
   ~~~
2. **coarse physical-carrier leakage**
   ~~~text
   ||R_n^phys y - R_n y||
   ~~~
3. **reconstruction-range defect**
   ~~~text
   ||J_n^L (R_n y) - J_n^R y||.
   ~~~

No whole-space cross-volume transfer compatibility is introduced.

---

## 8. #5120--#5124: projective geometry becomes one variance defect

### #5120 — geometric receiver for finite reconstruction

For each fixed (r,k), geometric (Cq^n) bounds for the three reconstruction residuals, plus a geometric beta-majorant bound, imply summability of every fixed orbit mismatch and hence feed the existing strong-limit closure chain.

No uniformity in Krylov depth is required.

### #5121 — distance tail to scale decay

A model-independent scalar bridge converts a locality / Dobrushin tail

~~~text
f_n <= C * rho^(D_n) / (1-rho)
~~~

with

~~~text
n <= D_n
0 <= rho < 1
~~~

into an ordinary scale-geometric (C' ho^n) bound and summability.

### #5122 — exact projection-variance identities

The reconstruction-range and coarse-physical leakage residuals are exact orthogonal projection norm losses:

~~~text
rangeResidual^2
  =
||y||^2 - ||R_n y||^2

physicalLeakage^2
  =
||R_n y||^2 - ||R_n^phys y||^2.
~~~

They telescope:

~~~text
rangeResidual^2 + physicalLeakage^2
  =
||y||^2 - ||R_n^phys y||^2.
~~~

Define the right-hand side as the **total reconstruction variance defect**.

### #5123 — one variance tail controls both projective residuals

A single tail

~~~text
V_n <= C * rho^(D_n) / (1-rho)
~~~

generates geometric bounds for both projection residuals, with rate (sqrt{ho}).  The independent geometric inputs are reduced to:

~~~text
physical transfer/reconstruction commutation
  +
total reconstruction variance tail
  +
beta majorant.
~~~

### #5124 — total variance is one common-marginal projection residual

The identity-instance of subspace-projected isometric compression is proved model-independently to be the canonical orthogonal projection onto the embedded subspace.

Specialized to adjacent SU(2) reconstruction:

~~~text
V_{n,r,k}
  =
||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2,
~~~

where (P_n^{phys}) is the orthogonal projection in the common finite marginal onto the coarse embedded completed physical pair carrier.

This is the key current interface: the projective part of H1-C3 geometry is now a standard Hilbert projection / conditional-variance problem.

---

## 9. Current H1-C3 model-facing frontier

The strong-limit implication chain is already formalized.  The remaining actual-model work is to prove quantitative decay for the following explicit quantities.

### A. Common-marginal physical projection variance

For each fixed (r,k), prove a locality / influence tail for

~~~text
V_{n,r,k}
  =
||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2.
~~~

Preferred route:

~~~text
coarse embedded physical range
  <-> suitable finite-marginal conditional-expectation fixed space
  ->
self-adjoint/idempotent projection comparison
  ->
finite Wilson conditional variances / influence kernel
  ->
Dobrushin geometric tail in support distance
  ->
#5121 distance-to-scale conversion
  ->
#5123 projective residual bounds.
~~~

The repository already contains substantial `condExpL2`, projection comparison, Wilson conditional-variance, and finite influence infrastructure.  The missing theorem is the exact model-facing identification/comparison at the adjacent common marginal.

### B. Physical transfer/reconstruction commutation

For the actual finite orbit vector (x_{n,r,k}), control

~~~text
||T_n R_n^phys x_{n,r,k}
  -
R_n^phys T_{n+1,beta_n} x_{n,r,k}||.
~~~

Only vector-wise control at fixed (r,k) is needed.  Whole-space operator convergence is still unnecessary.

This is the genuinely dynamical cross-volume geometry term.

### C. Explicit beta-majorant trajectory

Control

~~~text
C_norm(H_n,beta_n,beta_{n+1})
  * ||beta_{n+1}-beta_n||
~~~

by a summable or geometric sequence.

This is scalar and explicit; it is no longer an unidentified operator obstruction.

---

## 10. H1-C3 closure chain once A/B/C are supplied

For every fixed (r,k):

~~~text
A: total reconstruction variance tail
  -> #5123
projective residual geometric bounds

B: physical reconstruction commutation geometric bound

C: explicit beta-majorant geometric/summable bound

  -> #5120 / #5119
finite reconstruction residual summability

  -> #5118 / #5117
orbit geometry summability

  -> #5116 / #5115 / #5108
orbit mismatch summability

  -> #5106
fixed-m adjacent evolved defect summability

  -> #5098 / #5096
Cauchy and strong limit

  -> #5097
norm-one nonzero time-zero continuum excitation

  -> existing q0 receiver
||z_{infty,m}|| <= q0^m.
~~~

This closes all **fixed natural times** once the model-facing estimates A/B/C are proved.

A further theorem is then required to identify the fixed-(m) limits with iterates of one continuum discrete-time transfer operator.

---

## 11. H2 — physical-time scaling remains separate

The fixed natural-time factor

~~~text
q0 = 3071/3072
~~~

is not itself a continuum physical mass.

If lattice spacing (a_n 	o 0), then naively

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed (t>0).

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

Generic functional-analytic infrastructure is extensive.

The missing work is model-facing identification, decay, and scaling.

---

## 13. What is actual-model closed versus conditionally closed

### Actual-model closed

- finite (q_0) receiver;
- H1-D4;
- completed H1-D5 no-go;
- finite norm-one three-mode non-top excitation;
- time-zero continuum nontriviality once Cauchy data are supplied;
- adjacent common-marginal representation;
- orbit-wise telescoping receiver;
- one-slab and raw pair beta response;
- explicit normalization floor;
- normalized pair-transfer beta response;
- explicit adjacent beta coupling majorant;
- finite fine-to-coarse reconstruction map;
- exact projection-variance identities;
- total reconstruction variance = one common-marginal orthogonal projection residual squared.

### Closed as functional-analytic / receiver implication

- summable adjacent defects imply strong convergence;
- geometric orbit mismatch implies all fixed-natural-time limits;
- geometric finite reconstruction residuals imply orbit summability;
- one growing-distance total-variance tail controls both projective geometry residuals;
- growing support distance converts Dobrushin-style tails to refinement-scale decay.

### Not yet actual-model closed

- quantitative tail for the common-marginal physical projection variance;
- quantitative vector-wise physical transfer/reconstruction commutation;
- explicit chosen beta trajectory satisfying the required weighted summability/geometric criterion;
- identification of one limiting continuum discrete-time transfer operator;
- spacing-scaled physical-time dynamics;
- continuum OS Hamiltonian / Wightman mass gap.

---

## 14. Lean / CI engineering rules

Repository rules to preserve:

- fresh exact theorem-carrier SHA has highest authority;
- pinned Lean `v4.30.0-rc2` and pinned mathlib APIs are authoritative;
- inspect the whole changed Lean file, not only the first compiler error;
- separate mathematical failures from coercion / elaboration / typeclass failures;
- theorem-bearing PRs require exact-head Lean Fast Check success;
- theorem-bearing PRs require a matching exact-head receipt;
- do not rerun strict Lean for an unchanged already-GREEN exact head;
- docs-only changes do not require a redundant strict-Lean build.

Recent Lean 4 lessons from #5111--#5124:

- avoid `simpa` through huge dependent `ContinuousLinearMap` expressions;
- use `change` to normalize bundled-map coercions before rewriting;
- `J m`, `J.toLinearMap m`, and `J.toContinuousLinearMap m` may be definitionally equal but not syntactically identical for `rw`;
- check theorem orientation before `exact`; projection uniqueness lemmas may return the reverse equality;
- keep Pythagoras / scalar / projection hypotheses local and combine them with `calc`;
- do not import current-mathlib module paths that do not exist in the pinned commit;
- scope completeness assumptions to the declarations that actually need them;
- prefer existing `starProjection_apply_mem` and `sub_starProjection_mem_orthogonal` APIs over indirect range arguments.

---

## 15. Recent milestone ledger

| PR | Status | Main result |
| --- | --- | --- |
| #5108 | merged | orbit mismatch <= orbit geometry + coupling |
| #5109 | merged | exact one-slab kernel beta-Lipschitz |
| #5110 | merged | pair kernel/L2/raw pair transfer beta-Lipschitz |
| #5111 | merged | explicit normalization floor and inverse-square bound |
| #5112 | merged | physical transfer and transfer-norm beta-Lipschitz |
| #5114 | merged | normalized physical pair-transfer beta perturbation |
| #5115 | merged | explicit adjacent coupling beta majorant |
| #5116 | merged | eliminate abstract coupling residual from H1-C3 input |
| #5117 | merged | split orbit geometry by coarse-range projection |
| #5118 | merged | finite-carrier representation of orbit geometry |
| #5119 | merged | canonical fine-to-coarse reconstruction map |
| #5120 | merged | geometric receiver for three finite reconstruction residuals |
| #5121 | merged | growing-distance geometric tail -> scale decay |
| #5122 | merged | exact projection-variance identities and telescoping |
| #5123 | merged | one total variance tail controls both projective residuals |
| #5124 | merged | total variance = one common-marginal physical projection residual² |

---

## 16. Restart checkpoint

Latest theorem-bearing baseline before this docs refresh:

~~~text
28a58a37f2cb1da525a670e05bbece16867f3809
~~~

Read these files first:

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionCommonProjection.lean` — #5124
2. `RealLinearIsometrySubspaceProjectedCompressionProjection.lean` — #5124
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVarianceGeometric.lean` — #5123
4. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVariance.lean` — #5122
5. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionGeometric.lean` — #5120
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstruction.lean` — #5119
7. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryFiniteRepresentation.lean` — #5118
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatchSplit.lean` — #5108
9. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCouplingBetaMajorant.lean` — #5115
10. `PeriodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairBetaLipschitz.lean` — #5114
11. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison.lean` — conditional-expectation comparison infrastructure
12. `PeriodicHypercubicEvenCurrentInfluenceGeometricTail.lean` — finite influence geometric-tail infrastructure

Current handoff:

~~~text
CLOSED:
  finite uniform q0 receiver
  H1-D4
  completed H1-D5 no-go
  finite three-mode non-top excitation
  adjacent-Cauchy / fixed-time receiver chain
  normalized same-volume coupling response
  explicit adjacent beta majorant
  orbit geometry -> finite reconstruction reduction
  projective reconstruction residuals -> one total variance defect
  total variance defect -> one common-marginal orthogonal projection residual^2

NEXT — projective geometry:
  identify / compare the common physical projection with
  suitable finite-marginal conditional expectation(s)
  ->
  finite conditional variance / influence bound
  ->
  Dobrushin support-distance tail
  ->
  #5121 / #5123

NEXT — dynamical geometry:
  vector-wise finite physical transfer/reconstruction commutation
  ->
  locality / refinement estimate

NEXT — scalar trajectory:
  explicit geometric/summable weighted beta increments

THEN:
  #5120 -> #5119 -> #5118 -> #5117 -> #5116/#5108
  ->
  #5106 -> #5098/#5096
  ->
  all fixed-natural-time evolved strong limits
  ->
  continuum discrete-time transfer identification

THEN:
  H2 spacing-sensitive physical-time scaling

LATER:
  OS Hamiltonian
  ->
  spectral / Wightman mass gap.
~~~
