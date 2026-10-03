# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-03 JST

| Item | Value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique authoritative theorem-carrier | formal/real-hilbert-uniform-coercive-strong-limit |
| Fresh theorem-carrier HEAD | a72ba16e1e6a1596db974ee0c20b6ffc8d79c73b |
| Latest theorem merge | PR #5061 — positive-coupling SU(2) completed H1-D5 no-go |
| #5061 validated PR head | d8e08f83dc422a3d4636a01559afdffa5d176a21 |
| #5061 validation | PR Lean Fast Check 37117871784: completed / success; exact-head receipt success |
| Previous trace-span merge | PR #5059 — merge 4a318081c47a724c6ca92c9953f9a5067f91bf1b |
| Previous strict crossing merge | PR #5058 — merge d9b9de525c213739e9cdb145890c1f14e97b4f3b |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

The default branch main is a documentation mirror only and is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

README / ROADMAP-only merges are docs-only. They may move a branch pointer but do not replace the theorem-bearing baseline.

## 0. Current frontier in one page

The finite-volume gap problem and H1-D4 are closed. The old completed H1-D5 compatibility is now also closed, but as a no-go theorem rather than as a usable seam.

### Finite-volume input already closed

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||
~~~

on the full completed physical pair non-top sector.

H1-D4 gives exactly

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier
~~~

by #5029.

### #5061 closes the old H1-D5 seam

At beta > 0, #5058 proves strict temporal-crossing positivity for every nonzero finite primary normalized-trace polynomial in the exact half-weight endpoint measure. #5059 identifies the chosen continuous SU(2) two-mode carrier with span{1,r}. #5061 combines these facts for an arbitrary nonzero physical two-mode vector, proves feature-analysis kernel triviality on that span, and feeds it into #5045/#5044/#5043.

The resulting theorem is:

~~~text
beta(n) > 0
  ->
not completed H1-D5 compatibility at scale n.
~~~

There is also a wrapper using merely the existence of one positive-coupling finite scale.

Therefore completed H1-D5 is no longer an open compatibility problem and must not be reintroduced under an equivalent formulation.

### Immediate frontier

The next model-facing seam must be weaker and excitation-level. The first geometry to test is

~~~text
actual centered finite-OS excitation
  -> PhysicalPairCarrier
  -> TopTop^perp
  -> existing full-pair non-top q0 receiver
  -> q0^m decay.
~~~

This is the direct R1/R3 route. It avoids vacuum equality and therefore avoids the rank-one collapse exposed by #5041/#5061. If one of the two memberships cannot be theorem-generated directly, the next alternatives are a centered-sector-only comparison or a direct projective-dynamics comparison.

## 1. Closed finite-volume foundation

### 1.1 Leakage / Schur / renewal / twelve-spatial frame

The leakage, terminal recurrence, renewal, two-boundary propagation, complete-order, endpoint-swap and twelve-spatial layers are closed.

The final coercive estimate is

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f)

1/2304 <= kappa_12(s,beta).
~~~

### 1.2 Physical transfer gap

The physical centering interface gives

~~~text
1/3072 <= physical top-eigenspace transfer gap.
~~~

With

~~~text
q0 = 3071/3072
~~~

the normalized top-orthogonal transfer satisfies

~~~text
||R_n|| <= q0 < 1

||R_n^m x|| <= q0^m ||x||.
~~~

Status: CLOSED.

## 2. Carrier audit and projective lane

### 2.1 Independent-product carrier

The simultaneous independent-product carrier remains useful for finite-scale comparison.

However centered fresh-coordinate images become pairwise orthogonal across new coordinates, so a nonzero centered strong limit cannot arise from the naive independent-coordinate embedding.

Status: CLOSED obstruction.

### 2.2 Projective carrier

#4993--#4998 construct the scale-coherent projective finite-OS lane.

The important result is:

~~~text
exact projective finite-marginal coherence
  -> equal continuum images across scales
  -> nonzero coherent finite sequence has nonzero strong limit.
~~~

For the explicit centered SU(N) primary-plaquette finite-OS data, a nonzero centered projective strong-limit theorem is available under the projective cylinder/readout assumptions.

Status: kinematic continuum carrier CLOSED; evolved dynamics remains OPEN.

## 3. Explicit two-mode and full-pair q0 route

#4999--#5003 build the explicit SU(N) Wilson-energy two-mode family and continuous representatives.

#5004--#5009 transport q0 control to the full completed physical pair non-top sector.

The current preferred finite q0 theorem is the full-pair theorem, not the earlier one-sided lane.

## 4. Top-sector rigidity

#5010--#5012 prove:

~~~text
every nonzero nonnegative top mode is a.e. strictly positive,

every unit top mode has fixed sign,

TopEigenspace
  =
span(canonical nonnegative top mode)
  =
span(chosen normalized top vector).
~~~

#5013/#5016 lift this to the pair sector:

~~~text
TopTopClosure
  =
span(selected pair-top vector).
~~~

Status: CLOSED.

## 5. Canonical-sign finite OS vacuum

#5017 identifies the vacuum-normalized finite OS vacuum boundary image with the concrete Wilson boundary vacuum.

#5018 proves the corresponding pair is fixed by arbitrary independent primary/antipodal endpoint gauge transformations.

These results are concrete and no longer merely abstract OS statements.

## 6. H1-D4 closed — #5022--#5029

The previous roadmap listed H1-D4 as open. It is now fully closed.

### #5022

Prove

~~~text
PhysicalPairCarrier
  <=
IndependentEndpointGaugeFixedPairSector.
~~~

### #5023

Identify the algebraic pair Gauss projection range.

### #5024

Prove dense range of the real L2 external tensor map.

### #5025

Identify the real L2 tensor completion with product L2.

### #5026

Identify the completed pair Gauss projection range.

### #5027

Construct the left Riesz representative for product-L2 kernels.

### #5028

Descend independent gauge-fixed pairings through Gauss projection.

### #5029

Close the reverse inclusion and prove

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Consequences:

- the canonical-sign vacuum pair is in the completed physical pair carrier;
- the H1-D4 carrier seam is no longer a residual assumption;
- #5030 can reduce the old vacuum-normalized H1-D6 route to H1-D5 alone.

Status: CLOSED.

## 7. H1-D5 literal reduction — #5030--#5045

### 7.1 #5030 — H1-D6 reduced to H1-D5

With H1-D4 closed, the old vacuum-normalized route has only one remaining seam: H1-D5.

### 7.2 #5031--#5035 — remove abstractions

H1-D5 is successively rewritten as:

~~~text
physical matrix coefficient identity
  -> literal finite Wilson double integral
  -> finite Wilson boundary-vacuum moment
  -> unfixed positive-half path-kernel moment
  -> normalization-free path-kernel identity.
~~~

### 7.3 #5036/#5037 — path message

The unnormalized finite Wilson path message M_H is constructed and its matrix coefficients are identified with positive-half transfer powers.

### 7.4 #5038 — one-slab power identity

H1-D5 forces

~~~text
T^(H+3) = ||T||^2 T^(H+1).
~~~

This is already much stronger than a harmless vacuum normalization statement.

### 7.5 #5039/#5040 — strict-positive subtop obstruction

If a nonzero eigenmode satisfies

~~~text
T f = rho f,

0 < rho < ||T||,
~~~

then H1-D5 fails.

Compact positivity theorem-generates such a mode whenever the normalized top-orthogonal restriction R is nonzero.

Therefore

~~~text
H1-D5
  -> R = 0.
~~~

### 7.6 #5041 — rank-one consequence

Using the one-dimensional top eigenspace:

~~~text
H1-D5
  ->
normalized one-slab transfer
  =
top rank-one projection.
~~~

Equivalently for raw transfer,

~~~text
T
  =
||T|| |Omega><Omega|.
~~~

This is the conceptual warning that H1-D5 is likely too strong.

### 7.7 #5042--#5045 — finite two-mode obstruction

The rank-one consequence is converted to the explicit two-mode Wilson sector.

H1-D5 implies:

~~~text
two-mode Wilson Gram determinant = 0.
~~~

Equivalent forms already formalized:

~~~text
feature images linearly dependent,

feature-analysis map has nontrivial kernel
  on the explicit physical two-mode span.
~~~

Thus it is enough to prove strict nondegeneracy on one finite SU(2) two-mode block.

## 8. Rewrite the residual as positive-density crossing Gram — #5046--#5048

### #5046

Rewrite the two-mode Wilson determinant using the bare temporal-gauge crossing kernel and spatial half-weights.

### #5047

Expose each half-weight endpoint factor as a strictly positive density relative to one-slice Haar.

### #5048

Move the crossing Gram to the exact equivalent positive endpoint measure.

After #5048 the problem is purely:

~~~text
finite one-slice SU(2),
positive endpoint density,
bare temporal crossing kernel,
two-dimensional trace/Wilson sector.
~~~

No OS completion issue remains inside the local strictness calculation.

## 9. Protect a genuine selected Fock sector — #5049--#5051

### #5049

Choose the four canonical primary-spatial plaquette links and one common selected Fock/Taylor degree.

All residual spatial links retain their genuine degree-zero Wilson term.

The full crossing kernel minus this selected product is Schur positive semidefinite.

### #5051

Factor the selected product exactly as

~~~text
exp(-beta)^(residual-link count)
  *
genuine four-edge selected-degree Wilson kernel.
~~~

The residual scalar is strictly positive.

This gives a cancellation-free protected sector inside the exact bare crossing kernel.

## 10. One-slice positive-density trace strictness — #5052--#5054

### #5052

Construct an explicit section of the primary spatial plaquette holonomy.

Consequences:

- primary SU(2) Wilson energy has infinite range;
- normalized trace has infinite range;
- every finite initial trace-power family has nonzero Gram determinant under arbitrary finite density nonzero a.e.

### #5053

Specialize the Gram theorem to the exact H1-D5 half-weight endpoint measure.

### #5054

For every nonzero finite normalized-trace polynomial P, theorem-generate a strictly positive degree n with nonzero trace-power pairing.

No centering hypothesis is needed.

## 11. Lift scalar strictness to genuine four-edge strictness — #5055--#5057

### #5055

Define the one-slice cyclic normalized-relative-trace Hilbert feature.

A nonzero scalar trace-power pairing gives a nonzero cyclic Hilbert feature moment.

### #5056

Pull a cyclic dual probe back through the existing arbitrary-degree four-edge adjoint map.

Therefore

~~~text
nonzero cyclic feature moment
  ->
nonzero genuine four-edge feature moment
  ->
strictly positive four-edge weighted Gram.
~~~

### #5057

Specialize the genuine four-edge Gram strictness to the exact H1-D5 half-weight endpoint measure.

Status: CLOSED.

## 12. #5058 — strict bare crossing Gram

At beta > 0, the protected selected Fock sector is scaled by:

~~~text
positive selected Taylor coefficient
  *
positive residual degree-zero scalar.
~~~

The full crossing feature is realized as:

~~~text
Schur-PSD remainder
  direct-sum
protected selected degree.
~~~

A nonzero selected moment cannot cancel in this direct sum.

Thus for every nonzero finite primary normalized-trace polynomial P:

~~~text
0 <
  integral integral
    P(A) P(B)
    K_cross(A,B)
    dmu_half(A) dmu_half(B).
~~~

This is the strongest current local strictness theorem.

Status: CLOSED.

## 13. #5059 — continuous SU(2) two-mode trace span

The normalized-Haar Gram--Schmidt two-mode family has the same L2 span as the literal Wilson seed 1,E_W.

#5059 lifts this span equality to the chosen continuous representatives using injectivity of ContinuousMap.toLp.

For SU(2):

~~~text
span{continuous mode 0, continuous mode 1}
  =
span{1,E_W}
  =
span{1,r},
~~~

with

~~~text
r = normalized real trace = 1 - E_W.
~~~

Each chosen continuous mode therefore admits literal normalized-trace coefficients.

Status: CLOSED.

## 14. #5061 — completed H1-D5 no-go CLOSED

#5061 formalizes the full final finite-dimensional chain.

### 14.1 Arbitrary two-mode vector -> nonzero trace polynomial

For

~~~text
x != 0,
x in span{f0,f1},
~~~

the theorem produces c : Fin 2 -> R with c != 0 and identifies the ambient Haar-L2 class of x with

~~~text
P(r) = c0 + c1 r.
~~~

This uses the #5059 continuous span equality rather than explicit Gram--Schmidt coefficients.

### 14.2 Exact physical quadratic form -> #5058 crossing form

For any continuous representative p of a physical SU(2) vector, #5061 proves that the physical one-slab quadratic form is exactly the bare temporal-crossing quadratic form under the positive half-weight endpoint measure.

Specializing p to the degree-one trace polynomial above lets #5058 give strict positivity for every nonzero two-mode vector.

### 14.3 Feature-kernel triviality

Using

~~~text
<Tx,x> = ||A_phys x||^2,
~~~

strict crossing positivity yields

~~~text
x in two-mode span,
A_phys x = 0
  ->
x = 0.
~~~

Thus the physical feature-analysis operator is injective on the complete SU(2) two-mode physical span at beta > 0.

### 14.4 Completed compatibility no-go

The #5045/#5044/#5043 obstruction chain then gives

~~~text
beta(n) > 0
  ->
not H1D5CompletedCompatibility.
~~~

The repository also proves the corresponding exists-positive-scale wrapper.

Status: CLOSED. H1-D5 is not an assumption to prove anymore; it is a formally refuted candidate seam at positive SU(2) coupling.

## 15. After the H1-D5 no-go: redesign the model-facing seam

The old plan was:

~~~text
completed H1-D5 compatibility
  -> vacuum pair fixed by normalized physical transfer
  -> top-pair alignment
  -> centered q0.
~~~

But the current theorem chain shows that this compatibility forces rank-one collapse and conflicts with strict positive two-mode crossing structure.

#5061 has formalized the no-go. Do not try to resurrect the same statement.

A replacement bridge must be weaker.

Candidate directions:

### R1 — direct centered-pair route

Prove directly for the actual centered finite-OS excitation:

~~~text
x_centered in PhysicalPairCarrier

x_centered in TopTop^perp.
~~~

The carrier part is now helped by the exact H1-D4 equality.

The top-orthogonality part should be proved without identifying the periodic OS vacuum with the one-slab Perron state.

### R2 — centered-sector comparison only

Compare the actual finite OS transfer and physical pair transfer only after projection to the centered/top-orthogonal sector.

Avoid any statement that forces equality on the vacuum.

### R3 — direct finite-OS q0 estimate

Instead of passing through vacuum alignment, prove that the actual centered finite-OS vector lies in a receiver already controlled by #5006.

### R4 — projective-dynamics comparison

Compare evolved finite OS states in the projective carrier directly, with the finite q0 estimate as a norm bound, rather than demanding equality of vacuum states across two different finite constructions.

The correct replacement should be chosen from theorem geometry, not by reintroducing the failed H1-D5 premise under a new name.

## 16. H1-C3 — projective dynamics

The projective carrier already gives nonzero centered strong limits.

Required next dynamical sequence after the finite seam is corrected:

1. choose the explicit centered two-mode finite-OS sequence;
2. prove projective initial-state coherence;
3. prove coherence or strong convergence of the evolved finite sequence;
4. identify a limiting discrete-time operator;
5. transport

~~~text
||S_n^m x_n|| <= q0^m ||x_n||
~~~

to

~~~text
||T^m x|| <= q0^m ||x||.
~~~

This is still discrete-time control.

## 17. H2 — spacing-scaled continuum dynamics

The fixed q0 cannot itself be interpreted as a fixed physical-time mass rate when lattice spacing a_n tends to zero.

For fixed t > 0:

~~~text
q0^floor(t/a_n) -> 0.
~~~

That is instantaneous collapse, not a nontrivial strongly continuous physical-time semigroup.

Required target form is something like:

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent rescaled Dirichlet/generator lower bound.

Relevant existing modules include:

- PhysicalYangMillsFloorExponentialTransferTrajectory.lean
- PhysicalYangMillsDerivedDiscreteTransferRate.lean
- PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap.lean
- PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScalingRate.lean
- PhysicalYangMillsWilsonIntrinsicRateToPhysicalMass.lean

Status: downstream after corrected finite/projective dynamics.

## 18. H3 — OS reconstruction

After H1/H2 provide actual model data:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry/self-adjointness;
- closed Hamiltonian;
- correct vacuum-orthogonal excitation sector.

Generic functional-analytic infrastructure is already substantial.

Status: downstream.

## 19. H4 — spectral / Wightman mass gap

Final intended route:

~~~text
finite-volume coercivity
  -> corrected finite OS / physical excitation bridge
  -> scale-coherent projective dynamics
  -> spacing-scaled continuum semigroup
  -> OS Hamiltonian lower bound
  -> positive spectral gap
  -> Wightman / energy-momentum mass gap.
~~~

A finite-volume transfer gap is not by itself the final continuum mass-gap theorem.

## 20. Exact distinctions to preserve

### H1-D4 is closed

Do not continue to list independent gauge-fixed pair -> physical pair carrier as an open seam.

#5029 proves equality of the sectors.

### H1-D5 completed compatibility is formally refuted at positive SU(2) coupling

#5061 proves that the old completed compatibility cannot hold at any finite scale with beta > 0 under the concrete SU(2) hypotheses used by the H1-D5 chain. It should not be listed as an unresolved seam or reintroduced under an equivalent name.

### Strict crossing positivity remains local finite-volume information

#5058 by itself is a finite one-slice strictness theorem under the exact half-weight endpoint measure. #5059 supplies the continuous two-mode trace-span identification, and #5061 performs the exact physical-L2 / half-weight-crossing bridge needed to turn those local facts into the completed H1-D5 no-go. None of this by itself transports q0 dynamics to the projective continuum.

### Projective nonzero strong limit is not evolved q0 coherence

#4998 gives nonzero projective strong limits under the projective data.

It does not yet identify finite transfer powers with continuum dynamics.

### Fixed q0 is not physical mass

-log(3071/3072) is a discrete one-step rate, not automatically a continuum mass.

## 21. Lean / CI engineering

Latest theorem evidence:

~~~text
PR #5061 exact head:
  d8e08f83dc422a3d4636a01559afdffa5d176a21

PR Lean Fast Check:
  37117871784
  completed / success

exact-head receipt:
  success

merged theorem-bearing snapshot:
  a72ba16e1e6a1596db974ee0c20b6ffc8d79c73b
~~~

Previous strict-crossing evidence:

~~~text
PR #5058 exact head:
  10c7cfe0ebbaa51f9aa9f3a2d437230fcb1c33a7

PR Lean Fast Check:
  37115300163
  completed / success

exact-head receipt:
  success
~~~

Current Lean lessons:

- inspect every changed Lean file, not only the first compiler line;
- preserve the pinned mathlib API over current-master assumptions;
- avoid duplicate Fintype / module / inner-product instances on dependent carriers;
- use the literal finite carrier already present in the kernel definition when definitional equality is delicate;
- prefer explicit local equalities across let aliases;
- prefer calc + Finset.sum_congr + named rewrites to broad simp_rw for ContinuousMap.toLp transport;
- remember simp may fail when it makes no progress;
- use congrArg when rw cannot see through dependent integral or inner-product aliases;
- prefer pointwise operator equalities after extensionality;
- do not rerun strict Lean for an unchanged exact head that is already GREEN;
- docs-only changes are not theorem-bearing.

## 22. Milestone ledger — #5022 through #5061

| PR | Status | Contribution |
| --- | --- | --- |
| #5022 | merged | physical pair carrier included in independent gauge-fixed sector |
| #5023 | merged | algebraic pair Gauss projection range |
| #5024 | merged | dense range of real L2 external tensor |
| #5025 | merged | real L2 tensor completion = product L2 |
| #5026 | merged | completed pair Gauss projection range |
| #5027 | merged | left Riesz representative for product L2 kernels |
| #5028 | merged | gauge-fixed pairings descend through Gauss projection |
| #5029 | merged | H1-D4 closed: gauge-fixed pair sector = physical pair carrier |
| #5030 | merged | old H1-D6 reduced to H1-D5 |
| #5031--#5035 | merged | H1-D5 literal Wilson/path reduction |
| #5036--#5038 | merged | H1-D5 -> one-slab power identity |
| #5039--#5041 | merged | strict subtop obstruction; H1-D5 -> rank-one transfer |
| #5042--#5045 | merged | two-mode Wilson Gram / feature-kernel obstruction |
| #5046--#5048 | merged | half-weight crossing Gram under positive endpoint density |
| #5049 | merged | protect selected crossing Fock sector |
| #5050 | merged | SU(N) two-mode seed span |
| #5051 | merged | selected crossing sector factorization |
| #5052 | merged | one-slice positive-density trace Gram nondegeneracy |
| #5053 | merged | exact half-weight endpoint trace Gram |
| #5054 | merged | positive-degree trace moments |
| #5055 | merged | cyclic Hilbert feature moments |
| #5056 | merged | genuine four-edge Gram strictness |
| #5057 | merged | four-edge strictness at H1-D5 endpoint measure |
| #5058 | merged | strict bare crossing Gram at beta > 0 |
| #5059 | merged | continuous SU(2) two-mode span = normalized-trace span |
| #5061 | merged | arbitrary physical two-mode vector -> nonzero trace polynomial -> feature-kernel injectivity -> completed H1-D5 no-go |

PR #5019 was not merged and is not theorem authority.

## 23. Restart sequence

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

The latest theorem-bearing baseline at this checkpoint is:

~~~text
a72ba16e1e6a1596db974ee0c20b6ffc8d79c73b
~~~

Read these modules first for the current frontier:

1. PhysicalYangMillsWilsonVacuumNormalizedH1D5SU2NoGo.lean — #5061
2. PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical.lean — existing direct physical-pair bridge
3. the current centered finite-OS two-mode pair modules from #4999--#5009
4. the full physical pair non-top q0 receiver from #5006
5. the top/top orthogonality and one-dimensional top-sector modules from #5010--#5016
6. PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureKernelResidual.lean — historical no-go bridge, now closed
7. PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightCrossingGramStrict.lean — #5058
8. SpecialUnitaryWilsonEnergySU2ContinuousTwoModeTraceSpan.lean — #5059

Current restart target:

~~~text
CLOSED:
  finite q0^m
  full pair non-top q0^m
  projective nonzero centered strong-limit carrier
  top eigenspace simplicity
  pair top-top one-dimensionality
  H1-D4 gauge-fixed pair = physical pair carrier
  H1-D5 -> rank-one / two-mode degeneracy reductions
  exact positive-density half-weight crossing formulation
  selected Fock-sector protection and factorization
  trace / cyclic / four-edge positive-density strictness
  bare crossing strictness at beta > 0
  continuous SU(2) two-mode span = span{1,r}
  arbitrary physical two-mode vector -> nonzero trace polynomial
  physical feature-map injectivity on the two-mode span
  positive-coupling completed H1-D5 no-go

NEXT:
  actual centered finite-OS excitation
    -> PhysicalPairCarrier
    -> TopTop^perp
    -> existing full-pair non-top q0 receiver
    -> q0^m decay

FALLBACK:
  centered-sector-only comparison
  or direct projective-dynamics comparison

THEN:
  evolved projective coherence and q0 transport

THEN:
  spacing-scaled physical-time rate

LATER:
  OS Hamiltonian
  spectral/Wightman mass gap.
~~~
