# MGAP4D Roadmap

Status date: 2026-10-04 JST

Authoritative theorem branch:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Pinned environment:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

Latest theorem-bearing baseline before this docs refresh:

~~~text
28a58a37f2cb1da525a670e05bbece16867f3809
~~~

Fresh GitHub state always takes precedence over this document.

The GitHub default branch `main` is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

---

# A. Permanent closed foundations

## A1. Finite-volume transfer-gap receiver — CLOSED

The repository already proves the quantitative finite-volume core:

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap

q0 = 3071/3072 < 1

||R_n^m x|| <= q0^m ||x||
~~~

on the full completed physical pair non-top sector.

This is not the current bottleneck.

## A2. H1-D4 — CLOSED

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Independent endpoint gauge-fixedness is theorem-generated, not assumed.

## A3. Completed H1-D5 — CLOSED AS A NO-GO

Positive-coupling SU(2) formally refutes the old completed cross-scale H1-D5 route.

Do not reintroduce equivalent assumptions under new names:

- vacuum/top alignment;
- rank-one normalized transfer forcing;
- exact completed cross-scale transfer compatibility;
- OS-boundary transfer = physical pair transfer by fiat.

---

# B. H1-C3 continuum-existence reduction — current structure

The target is existence of all **fixed natural-time** limits for the selected non-top three-mode excitation.

The route has been reduced to vector-wise adjacent-scale data.

## B1. Cauchy/strong-limit receiver — CLOSED

The chain #5090--#5099 proves:

~~~text
summable adjacent defects
  ->
Cauchy in the continuum L2 carrier
  ->
strong limit
~~~

for each fixed natural time and fixed mode.

At time zero:

~~~text
||A_{infty,0} c|| = ||c||.
~~~

Thus a unit coefficient gives a norm-one nonzero continuum initial excitation once the adjacent defect route closes.

## B2. Orbit-wise telescoping — CLOSED

#5106 removes the need for whole-space operator-norm convergence:

~~~text
||A^m x - B^m y||
  <=
||x-y||
  +
sum_{r < m} ||(A-B)(B^r y)||.
~~~

For each fixed (r,k), only

~~~text
e_{n,r,k}
=
||(A_n^L-A_n^R)(A_n^R)^r v_{n,k}^R||
~~~

must be summable or geometrically small.

## B3. Orbit mismatch split — CLOSED

#5108:

~~~text
e_{n,r,k}
  <=
g_{n,r,k} + c_n.
~~~

The two sides have now been reduced separately.

---

# C. Coupling lane — functionally explicit

## C1. Kernel and raw transfer response — CLOSED

#5109--#5110:

~~~text
||K_gamma-K_beta||
  <=
B_H ||gamma-beta||

||P_gamma-P_beta||
  <=
2 B_H ||gamma-beta||.
~~~

## C2. Normalization denominator — CLOSED

#5111:

~~~text
m_H(beta)
  =
exp(-beta * globalActionBudget(H))

m_H(beta) <= ||T_phys(beta)||.
~~~

Therefore inverse and inverse-square normalization factors have explicit upper bounds.

## C3. Physical transfer norm response — CLOSED

#5112:

~~~text
||T_phys(gamma)-T_phys(beta)||
  <=
B_H ||gamma-beta||

|||T_phys(gamma)||-||T_phys(beta)|||
  <=
B_H ||gamma-beta||.
~~~

## C4. Normalized pair transfer beta response — CLOSED

#5114 combines C1--C3:

~~~text
||S_gamma-S_beta||
  <=
C_norm(H,beta,gamma) ||gamma-beta||.
~~~

## C5. Adjacent coupling majorant — CLOSED

#5115:

~~~text
c_n
  <=
C_norm(halfExtent(n+1), beta(n), beta(n+1))
  * ||beta(n+1)-beta(n)||.
~~~

#5116 theorem-generates the old coupling-summability input from this explicit scalar majorant.

### Remaining coupling task

Choose / prove a beta trajectory satisfying either:

~~~text
sum_n C_norm(...) ||Delta beta_n|| < infinity
~~~

or a geometric bound

~~~text
C_norm(...) ||Delta beta_n|| <= C q^n,
0 <= q < 1.
~~~

This is now a scalar trajectory problem, not an unidentified transfer-operator obstruction.

---

# D. Geometry lane — finite reconstruction reduction

## D1. Coarse-range projection split — CLOSED

#5117:

~~~text
g_{n,r,k}
  <=
refinement-commutation residual
  +
fine-range leakage residual.
~~~

## D2. Finite-carrier representation — CLOSED

#5118 shows the actual fine Krylov orbit and frozen-coupling output are exactly finite pair-Haar vectors embedded into the adjacent common marginal.

## D3. Canonical finite reconstruction — CLOSED

#5119 defines

~~~text
R_n : FinePair(n+1) -> CoarsePair(n)
~~~

and its physical version (R_n^{phys}).

The remaining geometry is represented by three explicit finite vector-wise residuals:

~~~text
A_n(r,k)
  =
||T_n R_n^phys x_{n,r,k}
  -
R_n^phys y_{n,r,k}||

B_n(r,k)
  =
||R_n^phys y_{n,r,k} - R_n y_{n,r,k}||

C_n(r,k)
  =
||J_n^L(R_n y_{n,r,k}) - J_n^R y_{n,r,k}||.
~~~

Interpretation:

- (A_n): physical transfer / reconstruction commutation;
- (B_n): coarse physical-carrier leakage;
- (C_n): coarse reconstruction-range defect.

---

# E. Projective geometry — reduced to one variance defect

## E1. Geometric receiver — CLOSED

#5120:

For each fixed (r,k), geometric bounds on (A_n,B_n,C_n), plus a geometric beta majorant, imply summability of every orbit mismatch.

No uniformity in (r) is required.

## E2. Distance-tail to scale conversion — CLOSED

#5121 converts

~~~text
f_n <= C * rho^(D_n)/(1-rho)
n <= D_n
0 <= rho < 1
~~~

to a refinement-scale geometric bound and summability.

This is designed for Dobrushin / locality tails.

## E3. Projection variance identities — CLOSED

#5122:

~~~text
C_n(r,k)^2
  =
||y||^2 - ||R_n y||^2

B_n(r,k)^2
  =
||R_n y||^2 - ||R_n^phys y||^2.
~~~

Hence

~~~text
B_n(r,k)^2 + C_n(r,k)^2
  =
V_{n,r,k}
  =
||y||^2 - ||R_n^phys y||^2.
~~~

## E4. One variance tail controls both projective residuals — CLOSED

#5123:

If

~~~text
V_{n,r,k}
  <=
C * rho^(D_n)/(1-rho),
~~~

then both (B_n) and (C_n) satisfy geometric bounds with rate (sqrt{ho}).

Therefore the independent geometry inputs reduce from three residuals to:

~~~text
A_n(r,k)
  +
V_{n,r,k}.
~~~

## E5. Common-marginal projection identity — CLOSED

#5124 proves model-independently that identity subspace-projected isometric compression is the canonical orthogonal star projection onto the embedded subspace.

Specialized to the SU(2) adjacent common marginal:

~~~text
V_{n,r,k}
  =
||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2.
~~~

Thus the projective reconstruction problem is now a standard ambient Hilbert projection residual problem.

---

# F. Immediate frontier 1 — conditional expectation / influence bound for V_n

This is the highest-priority projective-geometry theorem.

## F1. Identify or dominate P_n^phys by a finite-marginal conditional expectation

Current object:

~~~text
P_n^phys
=
orthogonal projection onto
coarse embedded completed physical pair carrier
inside the adjacent common marginal.
~~~

Need a theorem connecting this projection to one or more existing finite Wilson conditional-expectation projections.

Preferred forms:

~~~text
P_cond (P_n^phys Y) = P_n^phys Y
~~~

or an exact equality of fixed spaces / projections when available.

Avoid adding a new compatibility assumption.  The relation must be theorem-generated from the existing finite marginal / projective readout / physical carrier structure.

## F2. Apply projection minimality / conditional-expectation comparison

Available generic machinery includes:

~~~text
realHilbert_idempotent_symmetric_residual_sq_le_of_fixed
realHilbert_idempotent_symmetric_residual_sq_eq_defect
boundedColorNormalizedResidualEnergy_le_coarseProjectionResidual_sq
WilsonMarginalCondExpComparisonData
~~~

The intended direction is to compare

~~~text
V_{n,r,k}
=
||Y-P_n^phys Y||^2
~~~

with a finite conditional-expectation / conditional-variance quantity that can be estimated by locality.

Carefully check inequality direction.  Orthogonal projection onto a larger subspace gives a smaller residual.

## F3. Connect to finite Wilson influence

Use existing exact finite machinery:

- Wilson one-link conditional variances;
- heat-bath projection (P_e) / fluctuation (Q_e);
- Dobrushin influence matrices;
- support locality;
- influence-walk kernels;
- geometric Neumann tails.

Target schematic estimate:

~~~text
V_{n,r,k}
  <=
C_{r,k}
  * rho^(D_{n,r,k})/(1-rho).
~~~

## F4. Convert support distance to refinement scale

Prove

~~~text
n <= D_{n,r,k}
~~~

or a comparable linear-growth bound.

Then #5121 gives a scale-geometric variance tail, and #5123 gives geometric bounds for both projective residuals.

---

# G. Immediate frontier 2 — physical transfer/reconstruction commutation

The remaining genuinely dynamical geometry term is

~~~text
A_n(r,k)
=
||T_n R_n^phys x_{n,r,k}
  -
R_n^phys T_{n+1,beta_n} x_{n,r,k}||.
~~~

Only fixed-(r,k) vector-wise control is needed.

## G1. Preferred strategy

Do **not** attempt to prove whole-space

~~~text
||T_n R_n^phys - R_n^phys T_{n+1,beta_n}|| -> 0.
~~~

Instead work on the actual finite Krylov orbit.

Potential decomposition:

~~~text
finite support core
  +
additional fine coordinates outside the relevant causal/refinement neighborhood
  +
normalization/locality tail.
~~~

Use the explicit finite Wilson/projective cylinder structure whenever possible.

## G2. Desired output

For every fixed (r,k), prove either

~~~text
sum_n A_n(r,k) < infinity
~~~

or preferably

~~~text
A_n(r,k) <= C_{r,k} q_{r,k}^n,
0 <= q_{r,k} < 1.
~~~

Then #5120 consumes it directly.

---

# H. Immediate frontier 3 — beta trajectory

The scalar majorant is

~~~text
b_n
=
C_norm(halfExtent(n+1), beta(n), beta(n+1))
  * ||beta(n+1)-beta(n)||.
~~~

Need an actual trajectory theorem producing either summability or geometric decay.

Possible routes:

- explicit geometrically convergent beta trajectory;
- scale-dependent coupling trajectory with explicit control of the normalization-floor factors;
- a stronger asymptotic hypothesis stated directly on the weighted increments.

This task is independent of the cross-volume geometry once the explicit coefficient is fixed.

---

# I. H1-C3 final closure chain

Once F, G, and H are supplied, for each fixed (r,k):

~~~text
F:
common projection variance tail
  -> #5123
B_n and C_n geometric

G:
A_n geometric

H:
beta majorant geometric/summable

  -> #5120
finite reconstruction residual summability

  -> #5119 / #5118 / #5117
orbit geometry summability

  -> #5116 / #5115 / #5108
orbit mismatch summability

  -> #5106
fixed-time adjacent evolved defect summability

  -> #5098 / #5096
Cauchy and strong limit

  -> #5097
nonzero norm-one time-zero continuum excitation

  -> finite q0 receiver
||z_{infty,m}|| <= q0^m.
~~~

At this point H1-C3 is closed for every fixed natural time.

---

# J. Continuum discrete-time transfer identification

After fixed-(m) limits exist, they must be packaged into one continuum discrete-time operator.

Required items:

1. define the limiting excitation subspace;
2. prove the time-one limit is well-defined there;
3. prove compatibility with finite-time limits;
4. establish
   ~~~text
   T_infty^m z_infty,0 = z_infty,m;
   ~~~
5. preserve contraction and the (q_0^m) non-top bound.

Do not infer semigroup compatibility merely from separate fixed-(m) convergence.

---

# K. H2 — spacing-sensitive physical-time scaling

The fixed factor

~~~text
q0 = 3071/3072
~~~

cannot by itself define a nontrivial continuum physical-time semigroup.

If (a_n 	o 0),

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed (t>0).

Need scale-sensitive information such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent rescaled generator / Dirichlet / Poincare estimate.

Possible targets:

- one-step defect (1-q_n = O(a_n));
- rescaled generator convergence;
- scale-sensitive Rayleigh quotient;
- spacing-aware Dirichlet form convergence.

H2 remains logically separate from H1-C3.

---

# L. H3 — OS Hamiltonian

After a strongly continuous continuum contraction semigroup is available:

1. construct / identify the generator;
2. prove self-adjointness in the OS physical Hilbert space;
3. identify the vacuum eigenspace;
4. prove a positive lower bound on the vacuum-orthogonal spectrum.

Generic Hilbert-space / spectral infrastructure already exists in the repository.

---

# M. H4 — Wightman / energy-momentum mass gap

Only after H1--H3 are actual-model closed:

~~~text
OS Euclidean reconstruction
  ->
continuum Hilbert space
  ->
Hamiltonian / energy-momentum representation
  ->
vacuum-orthogonal spectral gap
  ->
positive physical mass gap.
~~~

Do not claim this stage before the model-facing continuum dynamics and scaling are established.

---

# N. Lean 4 / mathlib engineering guidance

## N1. Pinned APIs are authoritative

Do not use a current mathlib module path or theorem signature merely because it appears in current online documentation.

The repository is pinned to:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
~~~

Check the pinned environment or existing repository usage first.

## N2. Bundled maps and coercions

Lean may display definitionally equal applications differently:

~~~text
J x
J.toLinearMap x
J.toContinuousLinearMap x.
~~~

`rw` is syntactic enough that these differences can matter.

Use:

- `change`;
- local helper equalities;
- `calc`;
- explicit named arguments.

Avoid unfolding large maps just to force a rewrite.

## N3. Projection theorem orientation

Check exact theorem direction.

Example confirmed in #5124:

~~~text
Submodule.eq_starProjection_of_mem_orthogonal
~~~

returns the star-projection equality in the opposite direction from the first attempted goal.

Use `.symm` when appropriate rather than restructuring the whole proof.

## N4. Keep scalar / Hilbert identities local

Prefer:

~~~text
have hPyth : ...
have hNorm : ...
calc ...
~~~

over one large `rw` / `simpa` through dependent operator definitions.

## N5. Section-variable pruning

Lean omits section variables not present in generated declarations.

- inspect the actual theorem signature;
- pass dependent parameters explicitly when needed;
- scope completeness assumptions only where required.

## N6. Whole-file audit

When CI fails:

1. inspect the compiler error;
2. inspect the entire changed file;
3. inspect transitive imports if declarations collide;
4. distinguish mathematical failure from elaboration/coercion/typeclass failure;
5. remove linter warnings in touched files when practical;
6. rerun exact-head CI.

## N7. CI merge rules

For theorem-bearing PRs require:

~~~text
exact head unchanged
+
PR Lean Fast Check success
+
matching exact-head receipt success.
~~~

For docs-only PRs:

- strict Lean rerun is unnecessary if no Lean file changed;
- docs-only commits do not become theorem-bearing authority.

---

# O. Recent milestone ledger

| PR | Status | Contribution |
| --- | --- | --- |
| #5114 | merged | normalized physical pair-transfer beta perturbation |
| #5115 | merged | explicit adjacent coupling beta majorant |
| #5116 | merged | remove abstract coupling residual from external H1-C3 input |
| #5117 | merged | split orbit geometry by coarse-range projection |
| #5118 | merged | represent geometry residuals on finite carriers |
| #5119 | merged | canonical finite fine-to-coarse reconstruction |
| #5120 | merged | geometric receiver for finite reconstruction residuals |
| #5121 | merged | growing-distance tail -> scale-geometric decay |
| #5122 | merged | projection norm-loss identities and total variance |
| #5123 | merged | one total-variance tail controls both projective residuals |
| #5124 | merged | total variance = one common-marginal physical projection residual² |

---

# P. Immediate implementation order

## P1 — common physical projection / conditional expectation bridge

Prove the model-facing fixed-space / projection relation needed to compare

~~~text
P_n^phys
~~~

with existing finite-marginal conditional-expectation projections.

## P2 — total reconstruction variance locality bound

Use conditional variance and finite influence to prove

~~~text
V_{n,r,k}
  <=
C * rho^(D_n)/(1-rho).
~~~

## P3 — support-distance growth

Prove the relevant support distance grows at least with the refinement index.

Feed into #5121 and #5123.

## P4 — physical reconstruction commutation

Prove vector-wise (A_n(r,k)) geometric or summable control from actual finite Wilson/refinement data.

## P5 — beta trajectory

Produce a geometric / summable explicit weighted beta-increment majorant.

## P6 — close actual H1-C3 fixed-time strong limits

Use the existing receiver chain through #5120 -> #5108 -> #5098.

## P7 — continuum discrete-time transfer

Identify one limiting operator and prove iterate compatibility.

## P8 — H2 physical-time scaling

Introduce spacing-sensitive rates / generator control.

## P9 — OS Hamiltonian and spectral mass gap

Only after H1/H2 model data exist.

---

# Q. Restart instructions

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Expected theorem-bearing baseline at this docs checkpoint:

~~~text
28a58a37f2cb1da525a670e05bbece16867f3809
~~~

but fresh GitHub state always takes precedence.

Read first:

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionCommonProjection.lean` — #5124
2. `RealLinearIsometrySubspaceProjectedCompressionProjection.lean` — #5124
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVarianceGeometric.lean` — #5123
4. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVariance.lean` — #5122
5. `GeometricTailIndexGrowth.lean` — #5121
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionGeometric.lean` — #5120
7. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstruction.lean` — #5119
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryFiniteRepresentation.lean` — #5118
9. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCouplingBetaMajorant.lean` — #5115
10. `PeriodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairBetaLipschitz.lean` — #5114
11. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison.lean`
12. `PeriodicHypercubicEvenCurrentInfluenceGeometricTail.lean`

Current handoff:

~~~text
CLOSED:
  finite uniform q0 receiver
  H1-D4
  completed H1-D5 no-go
  finite norm-one non-top excitation
  fixed-time adjacent-Cauchy receiver chain
  normalized same-volume coupling response
  explicit adjacent beta majorant
  orbit geometry -> finite reconstruction
  two projective residuals -> one total variance defect
  total variance defect -> one common-marginal orthogonal projection residual^2

CURRENT FRONTIER A:
  common physical projection
  ->
  conditional expectation comparison
  ->
  finite conditional variance / influence
  ->
  support-distance geometric tail
  ->
  #5121 / #5123

CURRENT FRONTIER B:
  vector-wise finite physical transfer/reconstruction commutation

CURRENT FRONTIER C:
  explicit weighted beta-increment summability / geometric decay

THEN:
  #5120 -> #5119 -> #5118 -> #5117 -> #5116/#5108
  ->
  #5106 -> #5098/#5096
  ->
  all fixed-natural-time evolved strong limits
  ->
  continuum discrete-time transfer identification

THEN:
  H2 spacing-sensitive physical time

LATER:
  OS Hamiltonian
  ->
  spectral / Wightman mass gap.
~~~
