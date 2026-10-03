# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PRs #5077 and #5078

The finite-volume positive-coupling transfer-gap route remains closed with the explicit volume/rank/scale-uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The q0 estimate is available on the full completed physical pair non-top sector.

The main change since the #5061 documentation checkpoint is that the old completed H1-D5 seam has not been revived. Instead the repository now has two weaker post-no-go routes:

1. a canonical projected/local-coefficient route (#5063--#5076), and
2. a stronger finite-dimensional SU(2) Gram--Schmidt route opened by #5077.

The second route is now the preferred next target because it can avoid any vacuum/top fidelity assumption. PR #5078 has already closed its pure finite-dimensional core: two real scalar constraints on a unit vector in Euclidean R^3 have a common normalized solution by rank-nullity.

A complete continuum four-dimensional Yang--Mills existence theorem and Wightman mass-gap theorem are not yet claimed.

## Authority checkpoint — 2026-10-04 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing merge | 426ad4fe783d030a61687fbb123aca00b90a3d1d |
| Latest theorem-bearing branch tip | merge 426ad4fe783d030a61687fbb123aca00b90a3d1d; #5077 merged after #5078 and contains both theorem lines |
| #5077 | all SU(2) Wilson-energy Gram--Schmidt modes realized as physical endpoint pairs |
| #5077 validation | head aaa6d50c2da21461a76a6a0e6e2f9ee72b518998; run 37157037971 success; exact-head receipt success |
| #5078 | abstract Fin 3 two-functional unit-kernel selector |
| #5078 validation | head 61acb9b380ee3822e5574c1e9fd56e61cba5d64f; run 37156892868 success; exact-head receipt success |
| Pinned Lean | v4.30.0-rc2 |
| Pinned mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

The default branch main is not theorem authority. It is a documentation mirror.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

README / ROADMAP-only commits are docs-only and do not replace the latest theorem-bearing snapshot.

## Current claim boundary

### Closed

- beta = 0 physical transfer gap equals 1;
- positive-beta finite-volume coercivity;
- volume/rank/scale-uniform transfer-gap floor 1/3072;
- q0 = 3071/3072 and uniform q0^m decay;
- q0^m decay on the full completed physical pair non-top sector;
- one-dimensional finite physical top eigenspace;
- one-dimensional completed pair top-top block;
- scale-coherent projective L2 carrier;
- explicit SU(N) Wilson two-mode boundary representatives;
- H1-D4:
  independent endpoint gauge-fixed pair sector equals the completed physical pair carrier;
- positive-coupling SU(2) completed H1-D5 no-go;
- canonical projection of the actual centered pair to the physical non-top sector;
- theorem-generated nonzero projected centered excitation at every finite scale;
- common-projective embedding of projected non-top modes;
- fixed-mode infinite-subsequence extraction;
- exact rank-one top subtraction formula for projected common images;
- canonical-sign OS vacuum pair common-projective image equals constant one at every scale;
- pair-top convergence reduced to the scalar vacuum/top overlap criterion;
- stronger projected convergence criterion using only the local top coefficient;
- exact canonical OS-vacuum pair coefficient factorization through normalized positive-half transfer;
- exact one-slice formula for the local projected-top coefficient;
- all SU(2) Wilson-energy Gram--Schmidt modes realized as physical one-slice modes and physical endpoint pairs;
- the entire SU(2) Gram--Schmidt endpoint-pair family is orthonormal in pair Haar L2;
- the pure finite-dimensional #5078 selector: any two real linear functionals on Euclidean R^3 admit a common unit vector in both kernels.

### Not yet closed

- model-facing instantiation of the #5078 selector with the #5077 three-mode pair synthesis, OS-vacuum pairing and pair-top pairing;
- proof that the synthesized selector has exact unit pair norm and belongs to the completed pair non-top sector;
- projective strong convergence of that scale-dependent selected combination;
- coherence / strong convergence of evolved finite q0-controlled states;
- identification of a limiting discrete-time physical transfer on the nonzero continuum excitation;
- spacing-scaled physical-time dynamics;
- final OS Hamiltonian lower bound;
- Wightman / energy-momentum mass-gap theorem.

## 1. Finite-volume gap route

The finite-volume transfer analysis has already reached

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

1/2304 <= kappa_12(s,beta),

1/3072 <= physical transfer gap,

q0 = 3071/3072.
~~~

The corresponding top-orthogonal natural-power estimate is volume/rank/scale uniform.

The pair theory upgrades this to the full completed physical pair non-top sector.

This part is not the present bottleneck.

## 2. H1-D4 is closed

PRs #5022--#5029 prove

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Consequences:

- the canonical-sign finite OS vacuum pair is in the completed physical pair carrier;
- independent endpoint gauge fixedness is no longer an assumption;
- pair-carrier membership does not need the old H1-D5 compatibility.

## 3. The old H1-D5 seam is formally refuted

PRs #5031--#5061 expose the old completed compatibility as far too strong.

The chain is

~~~text
completed H1-D5
  -> finite Wilson path identity
  -> one-slab power identity
  -> vanishing top-orthogonal restriction
  -> rank-one normalized one-slab transfer
  -> two-mode Wilson Gram degeneracy
  -> nontrivial feature-analysis kernel.
~~~

PRs #5058/#5059/#5061 prove that the concrete positive-coupling SU(2) two-mode sector has strictly positive crossing quadratic form and an injective physical feature-analysis map.

Therefore

~~~text
beta(n) > 0
  ->
not completed H1-D5 at scale n.
~~~

Do not reintroduce the old compatibility, or an equivalent vacuum/top alignment statement, under a new name.

## 4. Post-no-go projected route — #5063--#5069

### #5063

The actual vacuum-normalized centered pair receives an exact scalar top-pair expansion.

This gives a strictly weaker excitation-level scalar seam than H1-D5.

### #5064

The old SU(2) global vacuum/top alignment route is explicitly excluded.

### #5065

Define the canonical completed TopTop and nonTop projections of the actual centered pair.

The projected vector is unconditionally:

- in the completed physical pair carrier;
- top-top orthogonal;
- therefore controlled by the existing q0^m estimate.

### #5066/#5067

Nonzero projected excitation is reduced to a finite OS-vacuum / physical-pair-top overlap.

That overlap is theorem-generated strictly positive.

Hence at every finite scale at least one selected projected centered Wilson mode is nonzero and already receives q0^m decay.

### #5068/#5069

The projected modes are embedded into one common projective continuum L2 carrier.

An infinite increasing subsequence can be chosen on which one fixed mode label remains nonzero.

This closes the finite nonzero-q0 excitation existence problem without H1-D5.

## 5. Projective strong-convergence reduction — #5070--#5074

### #5070

The projected common image has the exact form

~~~text
centered image
  -
<top image, centered image> * top image.
~~~

Therefore no independent scalar-convergence proof is required if both moving vectors converge.

### #5071

The uncentered Wilson pair common image is eventually exactly one fixed continuum mode.

Centered convergence is reduced to the OS-vacuum pair image and pair-top image.

### #5072

The canonical-sign OS-vacuum pair common-projective image is exactly

~~~text
1
~~~

at every scale.

Thus the vacuum part of centered convergence is completely closed.

### #5073

For unit pair-top common images,

~~~text
pair-top image -> 1 strongly
  iff
finite vacuum/top overlap -> 1.
~~~

This yields one valid conditional route, but it is stronger than necessary.

### #5074

A weaker Hilbert-space lemma removes the need for convergence of the moving top direction:

~~~text
c_n -> c,
||t_n|| = 1,
<t_n,c_n> -> 0
  ->
c_n - <t_n,c_n> t_n -> c.
~~~

Therefore it is enough to prove the finite local projected-top coefficient tends to zero.

This local criterion is the preferred interpretation of the #5070 projection formula.

## 6. Local coefficient factorization — #5075/#5076

### #5075

For arbitrary physical one-slice endpoint vectors x,y,

~~~text
<v_OS, x tensor y>
  =
<v_OS, omega tensor omega>
  *
<S_half x, y>,
~~~

where S_half is the normalized positive-half physical transfer and omega is the normalized one-slice top mode.

The finite partition normalization cancels exactly.

No H1-D5 compatibility or vacuum/top alignment is used.

### #5076

For the explicit primary Wilson two-mode pair f_k tensor 1, the local projected-top coefficient has the exact one-slice form

~~~text
a_k
  =
alpha_k * delta
  -
gamma^2 * m_k,
~~~

with

~~~text
alpha_k = <omega, f_k>,
delta   = <omega, 1>,
gamma   = <v_OS, omega tensor omega>,
m_k     = <S_half f_k, 1>.
~~~

This removes pair-Haar geometry from the local-coefficient problem.

It is useful diagnostically, but the next preferred route no longer needs to prove gamma -> 1.

## 7. #5077 — infinite SU(2) Gram--Schmidt family realized as physical pairs

PR #5077 extends the kinematic input from two special modes to the full theorem-generated SU(2) Wilson-energy Gram--Schmidt family.

For every mode index k and finite scale n, the repository now has:

- an explicit primary-spatial-plaquette continuous Wilson Gram--Schmidt observable;
- a gauge-invariant physical one-slice L2 vector;
- an exact ordered endpoint-pair identification with a decomposable physical pair;
- membership in the completed physical pair carrier;
- orthonormality of the whole endpoint-pair family after transport to pair Haar L2.

Schematically,

~~~text
u_{k,n}
  in PhysicalPairCarrier,

<u_{i,n},u_{j,n}> = delta_ij.
~~~

This is the kinematic input needed for the new three-mode route.

## 8. Preferred next route: instantiate the #5078 selector on three #5077 pair modes

Take the first three orthonormal physical pair modes at scale n:

~~~text
u_0,n, u_1,n, u_2,n.
~~~

For coefficients c in R^3 define

~~~text
X_n(c) = sum_{k<3} c_k u_k,n.
~~~

Define the two real linear functionals

~~~text
L_vac,n(c) = <v_OS,n, X_n(c)>,

L_top,n(c) = <Omega_pair,n, X_n(c)>.
~~~

Combine them into

~~~text
L_n : R^3 -> R^2.
~~~

PR #5078 already proves the abstract rank-nullity statement needed here: two real scalar functionals on Euclidean R^3 have a common unit kernel vector. Therefore, after packaging L_vac,n and L_top,n as the two functionals required by #5078, one obtains c_n with

~~~text
L_vac,n(c_n) = 0,
L_top,n(c_n) = 0,
||c_n|| = 1.
~~~

Then

~~~text
x_n := X_n(c_n)
~~~

has all of the desired finite properties at once:

~~~text
||x_n|| = 1                 by orthonormality,

<v_OS,n, x_n> = 0           by construction,

<Omega_pair,n, x_n> = 0     by construction,

x_n in PhysicalPairCarrier  by #5077,

x_n in PairNonTop           by one-dimensional TopTop,

||S_pair,n^m x_n||
  <= q0^m ||x_n||
  = q0^m.
~~~

Because the vacuum coefficient is already zero, vacuum centering does not change x_n.

The remaining work in this section is model-facing: define the three-mode synthesis map from #5077, prove its exact norm formula from orthonormality, and instantiate #5078 with the two physical pairings.

This avoids:

- completed H1-D5;
- vacuum/top alignment;
- gamma_n -> 1;
- decay of the #5076 fidelity defect.

## 9. Expected projective compactness step after the three-mode selector

The coefficient vectors c_n lie on the unit sphere in R^3.

Finite-dimensional compactness should provide a subsequence

~~~text
c_{n_j} -> c_infinity,
||c_infinity|| = 1.
~~~

The SU(2) Gram--Schmidt projective-cylinder machinery already gives coherent continuum realizations of every fixed mode.

For the first three fixed continuum modes U_0,U_1,U_2, one should then obtain

~~~text
Embed(x_{n_j})
  ->
sum_{k<3} c_infinity,k U_k
~~~

strongly.

Because the continuum modes remain orthonormal,

~~~text
||sum c_infinity,k U_k|| = 1.
~~~

So the limiting excitation is automatically nonzero.

This is stronger than the older fixed-two-mode pigeonhole route because nonzero norm is built into the coefficient normalization.

## 10. What the three-mode route does not yet solve

Even after the initial nonzero strong limit is constructed, the dynamical identification remains open.

The finite estimate

~~~text
||S_n^m x_n|| <= q0^m
~~~

does not by itself define a continuum operator T or prove

~~~text
||T^m x|| <= q0^m ||x||.
~~~

The evolved finite states must first be shown to live coherently in the same projective carrier, or otherwise converge strongly to an identified limiting discrete-time dynamics.

This is the next H1-C3 layer after the three-mode selection and compactness steps.

## 11. H1-C3 — projective dynamics

Required sequence:

1. theorem-generate the three-mode unit selector c_n;
2. construct the exact finite non-top unit pair x_n;
3. extract a coefficient-convergent subsequence;
4. prove the projective image of x_n has a nonzero strong limit;
5. prove coherence / strong convergence of the evolved sequence S_n^m x_n for fixed m;
6. identify a limiting discrete-time operator T;
7. transport

~~~text
||S_n^m x_n|| <= q0^m
~~~

to the continuum limit.

Only after this step does finite q0 become a theorem about actual continuum discrete-time dynamics.

## 12. H2 — physical-time scaling

The fixed discrete factor q0 is not itself the continuum mass.

If lattice spacing a_n tends to zero, then for fixed t > 0,

~~~text
q0^floor(t/a_n) -> 0.
~~~

That is an instantaneous-collapse scaling, not a nontrivial strongly continuous physical-time semigroup.

The continuum-time layer needs a spacing-sensitive statement such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent generator / Dirichlet lower bound.

Existing rate and scaling modules remain downstream tools for this stage.

## 13. H3/H4 — OS Hamiltonian and Wightman mass gap

After projective dynamics and physical-time scaling provide actual continuum model data, the remaining route is

~~~text
continuum physical Hilbert space
  ->
strongly continuous contraction semigroup
  ->
self-adjoint Hamiltonian
  ->
vacuum-orthogonal spectral lower bound
  ->
positive mass gap
  ->
Wightman / energy-momentum mass-gap theorem.
~~~

Generic functional-analytic infrastructure is already substantial, but these model-facing identifications are not yet closed.

## 14. Lean / CI engineering rules

Current repository rules:

- fresh exact theorem-carrier SHA has highest authority;
- pinned Lean v4.30.0-rc2 and pinned mathlib API take precedence over current-master examples;
- inspect every changed Lean file, not only the first compiler error;
- distinguish theorem-bearing commits from docs-only commits;
- use exact-head CI receipts before theorem PR merge;
- do not rerun strict Lean for an unchanged exact head that is already GREEN;
- docs-only changes do not require a redundant strict-Lean rebuild;
- prefer explicit named parameters when section-variable inference is fragile;
- prefer direct theorem terms / simpa using when rw cannot match through coercions;
- avoid brittle change steps across definitional aliases;
- preserve the direction of inner-product symmetry lemmas explicitly.

## 15. Recent milestone ledger

| PR | Status | Contribution |
| --- | --- | --- |
| #5061 | merged | positive-coupling SU(2) completed H1-D5 no-go |
| #5062 | merged | docs refresh through #5061 |
| #5063 | merged | centered-pair scalar replacement for the failed seam |
| #5064 | merged | exclude old SU(2) vacuum/top alignment route |
| #5065 | merged | canonical physical non-top projection of centered pairs |
| #5066 | merged | reduce projected nonzero to finite vacuum/top overlap |
| #5067 | merged | prove projected centered excitation nonzero at every scale |
| #5068 | merged | common projective embedding of projected modes |
| #5069 | merged | fixed nonzero mode on an infinite increasing subsequence |
| #5070 | merged | projected strong-convergence factorization |
| #5071 | merged | centered-image convergence reduced to OS vacuum pair |
| #5072 | merged | canonical OS vacuum pair projective image is exactly one |
| #5073 | merged | pair-top convergence iff vacuum/top overlap tends to one |
| #5074 | merged | local top-coefficient convergence criterion |
| #5075 | merged | OS vacuum pair coefficient = overlap times normalized half-transfer coefficient |
| #5076 | merged | exact one-slice local projected-top coefficient formula |
| #5077 | merged | full SU(2) Gram--Schmidt Wilson family realized as physical orthonormal endpoint pairs |
| #5078 | merged | abstract Euclidean R^3 two-functional common unit-kernel selector |

## 16. Restart checkpoint

Latest theorem-bearing baseline before this docs refresh:

~~~text
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Latest theorem PR evidence:

~~~text
PR #5077 exact head:
  aaa6d50c2da21461a76a6a0e6e2f9ee72b518998

PR Lean Fast Check:
  run 37157037971
  completed / success

exact-head receipt:
  success
~~~

Read these files first for the current frontier:

1. PhysicalYangMillsWilsonVacuumNormalizedProjectedLocalTopCoefficientCriterion.lean — #5074
2. PhysicalYangMillsWilsonVacuumNormalizedPairPositiveHalfTransferRatio.lean — #5075
3. PhysicalYangMillsWilsonVacuumNormalizedLocalTopOneSliceFormula.lean — #5076
4. PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean — #5077
5. RealEuclideanFinThreeTwoFunctionalKernel.lean — #5078
6. SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt.lean
7. PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCylinder.lean
8. PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadout.lean
9. the full physical pair non-top q0 receiver from #5006

Current restart target:

~~~text
THREE COHERENT ORTHONORMAL PHYSICAL PAIR MODES (#5077)
  +
ABSTRACT TWO-FUNCTIONAL UNIT-KERNEL SELECTOR (#5078)
  ->
instantiate with
  [vacuum pairing, pair-top pairing]
  ->
exact finite unit non-top excitation
  ->
existing q0^m receiver
  ->
coefficient-sphere subsequence
  ->
nonzero projective strong limit

THEN:
  evolved projective coherence
  ->
continuum discrete-time q0 dynamics

THEN:
  spacing-scaled physical-time rate

LATER:
  OS Hamiltonian
  ->
spectral / Wightman mass gap.
~~~
