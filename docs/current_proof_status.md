# Current proof status

**Updated:** 2026-06-28  
**Latest mathematical proof checkpoint on `main`:** PR #298, `923d47c997a9b1b59cfb6a87adc30fdc4fdeee9d`  
**Active physical branch:** PR #282, `509cfbe825ee635940b9fe5728fe1d437a376356`  
**Stacked operator-state branch:** PR #299, `6307a1b622749fcfbed89531893a0faa42b820a4`

## Status boundary

MGAP4D is a replayable Lean 4 / mathlib formal-development repository.

It does **not** yet prove an unconditional interacting four-dimensional continuum Yang--Mills theory, a fully instantiated physical Osterwalder--Schrader reconstruction, or an independently derived physical mass gap.

The current source must be read in three layers:

```text
main
  merged and replayable finite Wilson mathematics

PR #282
  large open physical probability / OS / Hamiltonian branch
  with conditional continuum constructors and gap-transfer theorems

PR #299
  open branch stacked on PR #282
  adding the vacuum operator vector functional
```

Open-PR theorems are not part of `main` until merged and replayed there.

A theorem that accepts a positive gap certificate as an argument is a conditional transfer theorem, not a proof that the physical model supplies that certificate.

## Main-branch mathematical state

The latest mathematical proof checkpoint on `main` is PR #298.

The documentation commits following that checkpoint do not change theorem bodies.

### Finite Gibbs, projection, and Hamiltonian structure

The merged source constructs:

- finite Wilson Gibbs probability mass functions;
- exact single-link conditional laws;
- Gibbs expectation and variance;
- conditional projection `P_e`;
- fluctuation projection `Q_e = I - P_e`;
- detailed balance and Gibbs symmetry;
- orthogonality and weighted Pythagoras;
- the concrete finite Gibbs Hilbert realization;
- the heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- the exact quadratic-form identity;
- the exact operator relation `H_HB = |E| (I - P_scan)`.

### Legacy canonical Dobrushin-to-Rayleigh route

The legacy finite interface proves:

```text
exact conditional-TV influence
  -> exact row sums and alpha_can
  -> variation contraction
  -> random-scan iterate contraction
  -> centered fixed-point triviality
  -> nonconstant eigenvalue control
  -> Gibbs-Hilbert spectral lift
  -> centered Rayleigh contraction
  -> finite Hamiltonian-gap consequences.
```

The implication from `alpha_can < 1` to the centered `L2`/Rayleigh and finite Hamiltonian statements is therefore closed.

The remaining quantitative problem is to prove a physically relevant strict estimate for the intended approximation family.

### Plaquette support and periodic geometry

The merged source proves:

```text
alpha_can <= d_active * eta_active,

eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

It also proves exact remote-factor cancellation, zero influence outside plaquette support in the legacy interface, and localization of source dependence to shared plaquettes.

For the signed periodic four-dimensional hypercubic geometry and side length `n >= 3`, it proves

```text
d_active <= 18,
m_shared <= 1.
```

The side-length restriction is mathematically necessary because wrapping at `n = 2` can create two shared plaquettes for distinct parallel links.

### Orientation-correct physical-link route

PRs #289 and #293--#298 are merged.

They add:

- one configuration variable per positive physical link;
- signed forward/backward plaquette traversal;
- physical-link replacement;
- agreement away from the replaced source link;
- signed plaquette-holonomy congruence;
- non-neighbor locality;
- target-local / target-remote action decomposition;
- exact oriented single-link Boltzmann weights;
- the finite conditional partition function;
- the normalized conditional PMF;
- local and remote Boltzmann factors;
- exact weight and partition-function factorization;
- exact cancellation of the common remote factor;
- identification of the conditional law with `finiteNormalizedExp`;
- the oriented conditional total-variation seminorm;
- the sharp TV bound from mutual exponential ratios;
- the local-action-oscillation bound;
- the exact oriented canonical influence by finite enumeration;
- nonnegativity and exact zero diagonal;
- the active-source exponential-ratio influence bound.

The principal new files are:

```text
FiniteOrientedLatticeWilsonSingleLinkConditional.lean
FiniteOrientedLatticeWilsonConditionalWeightFactorization.lean
FiniteOrientedLatticeWilsonConditionalRemoteCancellation.lean
FiniteOrientedLatticeWilsonConditionalNormalizedExp.lean
FiniteOrientedLatticeWilsonConditionalActionOscillationTV.lean
FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence.lean
FiniteOrientedLatticeWilsonCanonicalInfluenceBound.lean
```

### Remaining finite oriented bridge

The following are not yet merged:

- coefficient-level inactive-source zero influence in the oriented interface;
- exact oriented row sums;
- an oriented canonical coefficient;
- the active-neighbor row-sum estimate;
- direct transport of periodic incidence bounds into that coefficient;
- connection of the oriented coefficient to the existing random-scan/Rayleigh/Hamiltonian API;
- the explicit periodic oriented `Z2` strict-parameter theorem.

## Active PR #282

### Repository state

PR #282 is open, non-draft, and currently reported as mergeable.

At the recorded head:

```text
head: 509cfbe825ee635940b9fe5728fe1d437a376356
commits: 1315
changed files: 334
additions/deletions: +42411/-0
```

Current-head workflows:

- **PR Lean Fast Check**, run 4698: queued;
- **Temporary Concrete Wilson OS Boundary Gap Check**, run 113: queued;
- **Temporary Exponential Boundary Poincare Check**, run 30: queued.

The branch contains temporary workflows and is not treated as merge-ready.

This CI receipt is volatile and is not a theorem statement.

### Finite periodic `SU(N)` Wilson theory

The branch constructs actual finite-volume laws rather than only abstract convergence wrappers.

It contains:

- orientation-correct compact gauge Wilson systems;
- normalized compact Haar product measure;
- the Wilson Gibbs density and probability measure;
- finite-volume gauge invariance;
- arbitrary periodic translation invariance;
- concrete integer temporal translations;
- exact periodic geometry bridges;
- exact counts

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4;
```

- specialization to `Matrix.specialUnitaryGroup (Fin N) C`;
- the standard Wilson energy

```text
E_W(U) = 1 - Re(trace U) / N;
```

- continuity, conjugation invariance, and inversion compatibility;
- the bound `0 <= E_W(U) <= 2`;
- deterministic normalized Wilson-action control.

The deterministic action bound is not a derivation of the physical renormalized coupling trajectory.

### Physical weak-limit route

A common-carrier embedding packages:

- actual finite periodic `SU(N)` Gibbs laws;
- measurable interpolation into one Polish carrier;
- lattice spacing tending to zero;
- physical volume tending to infinity.

Given a proper physical functional and a coercive pointwise estimate, the branch generates:

- uniform moment control;
- Markov tails;
- compact containment;
- tightness;
- a Prokhorov subsequence;
- a `PhysicalFourDimensionalYangMillsWeakLimit`;
- convergence of bounded continuous expectations.

This route remains conditional on the supplied physical carrier, interpolation or blocking maps, proper functional, coercive estimate, and scaling data.

### Gauge symmetry, translations, observables, and states

Under compatible continuous actions and interpolation equivariance, the branch proves:

```text
map(action g, mu_YM) = mu_YM.
```

Consequences include:

- invariant event probabilities;
- invariant laws of measurable observables;
- invariant bounded-continuous expectations;
- two-point and connected-correlation invariance;
- finite n-point invariance and convergence;
- a real algebra of gauge-invariant bounded continuous observables;
- normalized positive expectation states;
- weak-star convergence of lattice states.

The discrete temporal layer now includes:

```text
latticeTime(n,k) = k * latticeSpacing(n)
  + positive lattice spacing tending to zero
  -> floor-based dense temporal approximation.
```

Joint continuity then supplies a constructor transferring exact lattice-time invariance to all real continuum times.

This is a constructor from explicit compatibility and continuity data.

It does not produce those physical data automatically.

### Concrete finite even-periodic reflection positivity

PR #282 has advanced beyond the former abstract boundary-fibered scaffold.

It now contains:

- even-periodic time reflection;
- positive, negative, and fixed-boundary edge sectors;
- boundary/open-half coordinate equivalences;
- normalized Haar inversion and orientation correction;
- boundary-fibered product-Haar factorization;
- Wilson Gibbs density factorization;
- temporal and spatial crossing-sector analysis;
- exact Wilson Boltzmann products;
- local positive-semidefinite Wilson kernels;
- finite tensor-product RKHS and Bochner-Gram constructions;
- observable integral transport;
- bounded-continuous finite Wilson Gibbs reflection positivity.

The finite reflection-positive theorem is implemented on the branch.

It is not yet merged on `main`.

### Weak-limit reflection positivity and OS Hilbert completion

Given the stated finite-to-continuum pullback bridges, the branch transfers finite reflection-form nonnegativity through weak-star convergence.

From supplied gauge-invariant reflection-positive state data, it constructs:

- the positive-time observable subalgebra;
- the OS bilinear form;
- the null-space quotient;
- the real pre-Hilbert carrier;
- the Hilbert completion;
- the normalized vacuum;
- a dense physical-state map.

Full continuum reflection positivity for every intended physical observable still depends on the concrete bridge and observable-identification data.

### Positive-time semigroup and closed Hamiltonian

From positive-time translation, contraction, reflection exchange, and observable-state continuity, the branch constructs:

- a contraction semigroup on the OS carrier;
- its bounded extension to the Hilbert completion;
- strong continuity;
- the canonical right-generator domain;
- the right infinitesimal generator;
- the right Hamiltonian `H = -G`;
- density of the generator and Hamiltonian domains;
- the zero-energy vacuum relation;
- closability;
- graph closure as a `LinearPMap`;
- nonnegativity of the closed Hamiltonian;
- positive-shift lower bounds and closed range;
- finite-time Laplace resolvents;
- positive-shift surjectivity and bijectivity;
- formal symmetry from reflection/time-translation exchange;
- self-adjointness of the graph-closed Hamiltonian.

These statements are theorem-generated from the explicit covariance and continuity structures.

The final physical model must instantiate those structures.

## Conditional mass-gap closure in PR #282

### Decisive finite-side input

The current direct certificate stores a positive real number `mass` and requires the scale-uniform shared-boundary estimate

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2
```

for every approximation scale, nonnegative time, and relevant boundary `L2` vector.

The certificate also contains:

- reflection/time-translation exchange;
- finite open-half measure;
- measurability and integrability of the Gram features and boundary moments;
- a boundary transfer operator;
- an intertwining identity between boundary transfer and half-time OS translation.

An alternative measurable feature-factorized interface asks for analysis and synthesis operators whose norm product yields the required strict contraction.

### Generated continuum consequences

Given that certificate and continuum observable-state strong continuity, the branch proves:

```text
finite exponential boundary Poincare estimate
  -> integrated boundary moment gap
  -> continuum half-time OS quadratic gap
  -> self-adjoint graph-closed OS Hamiltonian
  -> vacuum-orthogonal Rayleigh lower bound with exact mass
  -> zero-energy eigenspace equals the vacuum line
  -> no nonzero eigenvector in the interval (0, mass).
```

In particular, for Hamiltonian-domain vectors orthogonal to the vacuum, it derives

```text
mass * ||psi||^2 <= <H psi, psi>.
```

It also derives

```text
H psi = 0
  iff
psi = <psi, Omega> Omega.
```

### Current mathematical boundary

The scale-uniform strict Wilson boundary estimate is **not** currently proved for the physical approximation family.

Therefore:

- the positive mass is not yet generated from Wilson dynamics;
- the conditional mass-gap closure is not an unconditional physical mass-gap theorem;
- vacuum uniqueness is conditional on the same positive-gap transfer package;
- no numerical identification with `33/20` is established.

This distinction is the central claim boundary of the current branch.

## PR #299

PR #299 is open and stacked on PR #282.

It constructs the physical vacuum vector functional

```text
omega_Omega(T) = <Omega, T Omega>
```

on bounded real-linear operators over the completed real OS Hilbert space.

The branch proves:

- linearity in the bounded operator;
- identity expectation equal to `||Omega||^2`;
- normalization for the normalized OS vacuum;
- nonnegativity on the Hilbert quadratic positive cone.

It does not yet prove:

- complexification;
- weak-operator normality;
- faithfulness;
- construction of a local von Neumann algebra;
- cyclic-separating standard form;
- type-III classification;
- modular or relative-modular theory.

PR #299 is not on `main` and should be rebased or folded only after PR #282 is stabilized.

## Exact `33/20` dependency boundary

The source tree contains the internal normalized value

```lean
hamiltonianPVMSpectralNormalized3320Value := (33 : Real) / 20
```

and transports it through older spectral and audit interfaces.

The current physical OS Hamiltonian branch does not prove that its mass parameter equals `33/20`.

It also does not derive `33/20` from:

- the finite Wilson Gibbs law;
- the scale-dependent coupling trajectory;
- the boundary transfer operator;
- the continuum weak limit;
- the reconstructed physical Hamiltonian;
- physical dimensional units.

Thus `33/20` remains an internal normalization and dependency-routing value.

See `docs/exact_gap_layer_separation.md`.

## Claim table

| Claim | Status |
|---|---|
| Finite Wilson Gibbs law | proved on `main` |
| Finite conditional projections and Gibbs Hilbert space | proved on `main` |
| Legacy canonical Dobrushin-to-Rayleigh theorem | proved on `main` |
| Periodic bounds `d_active <= 18`, `m_shared <= 1` | proved on `main` for `n >= 3` |
| Orientation-correct exact conditional PMF | proved on `main` |
| Oriented local/remote cancellation | proved on `main` |
| Oriented normalized-exponential conditional law | proved on `main` |
| Oriented exact canonical influence and active bound | proved on `main` |
| Oriented canonical row-sum coefficient | open |
| Direct oriented coefficient-to-Hamiltonian bridge | open |
| Explicit periodic oriented `Z2` strict theorem | open |
| Finite periodic `SU(N)` Haar--Gibbs law | implemented in PR #282 |
| Finite periodic `SU(N)` reflection positivity | implemented in PR #282 |
| Physical weak-limit extraction | conditional in PR #282 |
| Continuum gauge and translation invariance | conditional in PR #282 |
| Gauge-invariant OS Hilbert completion | conditional in PR #282 |
| Closed nonnegative self-adjoint OS Hamiltonian | conditional in PR #282 |
| Positive continuum Rayleigh lower bound | conditional on a positive boundary-gap certificate |
| Unique zero-energy vacuum line | conditional on the same certificate |
| Exclusion of eigenvalues in `(0, mass)` | conditional on the same certificate |
| Scale-uniform strict Wilson boundary estimate | open |
| Concrete physical carrier and scaling trajectory | open |
| Nontrivial interacting continuum theory | open |
| Complete OS/Wightman reconstruction | open |
| Independent physical derivation of `33/20` | open |
| Final ordinary CI green for PR #282 | not established at this snapshot |
| External mathematical consensus | not claimed |

## Immediate next steps

1. Complete the oriented row-sum/coefficient layer on `main`.
2. Connect the oriented coefficient to the existing Dobrushin/Rayleigh/Hamiltonian spine.
3. State the explicit periodic oriented `Z2` finite theorem.
4. Obtain ordinary green CI for PR #282 and remove temporary workflows.
5. Split PR #282 into reviewable merge units.
6. Merge the finite `SU(N)` probability and reflection-positive layers.
7. Instantiate the physical carrier, interpolation, scaling, temporal/reflection covariance, and strong continuity.
8. Prove the scale-uniform strict Wilson boundary estimate or an equivalent factorized operator-norm estimate.
9. Apply the existing conditional continuum Hamiltonian-gap closure.
10. Prove nontriviality, complete OS/Wightman reconstruction, derive physical normalization, and obtain independent review.

## Public wording

A precise current description is:

```text
MGAP4D is a Lean 4 formal-development repository for the four-dimensional
Yang--Mills existence and mass-gap problem. The main branch proves a substantial
finite Wilson Gibbs, heat-bath Hamiltonian, Dobrushin-to-Rayleigh, periodic
four-dimensional geometry, and orientation-correct conditional-influence spine.
Open PR #282 additionally constructs periodic SU(N) Haar--Gibbs laws, concrete
finite reflection positivity, conditional continuum weak limits, an OS Hilbert
and self-adjoint Hamiltonian route, and a theorem transferring a supplied
scale-uniform boundary Poincare estimate to a positive continuum Hamiltonian
gap and a unique vacuum line. The scale-uniform physical estimate, final carrier
and scaling construction, nontriviality, complete reconstruction, and an
independent numerical mass-gap derivation remain open.
```

Lean theorem bodies are authoritative.

Conditional bridge structures, queued or temporary CI, internal numerical carriers, and unmerged branch source must not be presented as unconditional physical results.
