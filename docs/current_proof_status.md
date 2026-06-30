# Current proof status

**Updated:** 2026-06-30  
**Latest mathematical proof checkpoint on `main`:** `a80a75449a16d07889519c1823595c5244824583`  
**Latest merged mathematical proof PR:** PR #300  
**Current stacked frontier:** PR #328, `540cc5848626fce2a69fff6948e14886e9591277`  
**Frontier base carrier:** `formal/real-hilbert-uniform-coercive-strong-limit`, `a846a06aa286f4d0beb624bfd5e461653b797b58`

## Status boundary

MGAP4D is a replayable Lean 4 / mathlib formal-development repository.

It does **not** yet prove:

- an unconditional interacting four-dimensional continuum Yang--Mills theory;
- a nontrivial continuum measure obtained from one fully specified physical scaling trajectory;
- a physical positive mass gap derived from that trajectory;
- a complete instantiated Osterwalder--Schrader and Wightman reconstruction;
- a physical numerical mass value equal to `33/20`;
- external mathematical consensus on a Clay-problem solution.

The repository currently has two proof surfaces.

```text
main
  authoritative merged source
  replayable finite Wilson mathematics
  conditional continuum and OS theorem generators

stacked proof frontier
  post-checkpoint finite L2, strong-limit, OS defect,
  graph-core, and strong-resolvent development
```

A branch merged into another branch inside the stack is not thereby merged into `main`.

A theorem whose hypotheses include a positive mass, a strict Dobrushin coefficient, a scale-uniform Poincare estimate, a coercive compactness estimate, or a physical interpolation package is conditional until those hypotheses are constructed for the actual physical approximation family.

## Stable repository snapshot

### Latest mathematical checkpoint on `main`

```text
checkpoint:
  a80a75449a16d07889519c1823595c5244824583

latest mathematical proof PR:
  PR #300

large physical construction merged earlier:
  PR #282
  merge commit ed42e5af631aec11f16c7095c3cd892b488bd04d
```

PR #282 placed the finite `SU(N)`, weak-limit, reflection-positive, OS Hilbert, Hamiltonian, and conditional mass-gap construction on `main`.

PR #300 merged the orientation-correct canonical Dobrushin coefficient, compact Wilson coefficient-to-gap route, and related finite heat-bath and resolvent infrastructure.

Documentation-only commits after this checkpoint do not change the mathematical theorem bodies described below.

### Stacked frontier

```text
frontier PR:
  PR #328 — Prove full OS strong-resolvent convergence

head:
  540cc5848626fce2a69fff6948e14886e9591277

base branch:
  formal/real-hilbert-uniform-coercive-strong-limit

base commit:
  a846a06aa286f4d0beb624bfd5e461653b797b58
```

At this snapshot, PR #328 is open, non-draft, and reported as mergeable.

The **PR Lean Fast Check** run 5141 is in progress.

Relative to the latest mathematical checkpoint `a80a7544…`, the frontier is reported as:

```text
ahead:       237 commits
behind:      157 commits
merge base:  929e20583ae368475d4bedb65c060c2d3c4c0fff
```

The frontier therefore requires rebase, duplicate-file reconciliation, and reviewable decomposition before mathematical promotion to `main`.

## Mathematical state on `main`

## 1. Finite compact Wilson probability theory

The merged source constructs a finite periodic compact-gauge Wilson model using one configuration variable per positive physical link and inverse group elements for backward plaquette traversal.

It includes:

- normalized compact Haar product probability;
- Wilson Gibbs density and probability measure;
- finite gauge invariance;
- periodic translation invariance;
- integer temporal translations;
- exact periodic geometry bridges and counts;
- specialization to `Matrix.specialUnitaryGroup (Fin N) C`;
- the standard Wilson plaquette energy

```text
E_W(U) = 1 - Re(trace U) / N;
```

- continuity, conjugation invariance, and inversion compatibility;
- the deterministic bound

```text
0 <= E_W(U) <= 2.
```

These deterministic finite-volume bounds do not derive the renormalized coupling trajectory of continuum Yang--Mills theory.

## 2. Finite even-periodic reflection positivity

The merged source contains:

- even-periodic time reflection;
- positive, negative, and fixed-boundary edge sectors;
- boundary and open-half coordinate equivalences;
- Haar inversion and orientation correction;
- product-Haar factorization;
- Wilson Gibbs density factorization;
- temporal and spatial crossing-sector decomposition;
- exact Wilson Boltzmann products;
- local positive-semidefinite Wilson kernels;
- finite Hilbert and Bochner--Gram constructions;
- observable integral transport;
- bounded-continuous finite Wilson Gibbs reflection positivity.

This is a finite-volume theorem on `main`.

Continuum reflection positivity for the full intended physical observable class still requires explicit carrier, interpolation, observable-identification, and convergence data.

## 3. Orientation-correct Dobrushin coefficient

The merged physical-link lane contains:

- signed forward and backward plaquette traversal;
- physical-link replacement and off-link agreement;
- target-local and target-remote action decomposition;
- exact oriented one-link conditional laws;
- local and remote Boltzmann factorization;
- exact remote-factor cancellation;
- normalized-exponential representation;
- conditional total-variation bounds from local action oscillation;
- exact canonical influence and zero diagonal;
- zero influence outside plaquette support;
- exact row sums;
- the canonical Dobrushin coefficient;
- proof-relevant Dobrushin matrix data;
- active-neighbor coefficient majorants.

Principal merged files include:

```text
FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence.lean
FiniteOrientedLatticeWilsonCanonicalInfluenceSupport.lean
FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient.lean
FiniteOrientedLatticeWilsonDobrushinMatrix.lean
FiniteOrientedLatticeWilsonActiveCoefficientBound.lean
FiniteOrientedLatticeWilsonFourDimensionalDobrushinCertificate.lean
```

For periodic four-dimensional geometry with side length at least three, the source supplies:

```text
d_active <= 18,
m_shared <= 1.
```

The side-length restriction avoids periodic degeneracies present at side length two.

## 4. Finite heat-bath Hamiltonian consequences

The merged source closes the theorem-generating route

```text
strict canonical Dobrushin coefficient
  -> variation contraction
  -> random-scan contraction
  -> centered Rayleigh and Poincare inequality
  -> finite heat-bath Hamiltonian gap
  -> vacuum-sector coercivity
  -> lower real spectral enclosure
  -> real resolvent and inverse-norm bounds.
```

It contains finite Gibbs Hilbert realizations, normalized vacuum sectors, conditional projections, fluctuation operators, random-scan operators, and normalized heat-bath Hamiltonians.

The strict condition remains an input for a physical continuum approximation family.

A finite small-coupling estimate is not automatically uniform along a continuum weak-coupling or asymptotically free trajectory.

## 5. Conditional physical weak-limit construction

The merged common-carrier interface accepts:

- a suitable physical carrier;
- measurable interpolation, smearing, or blocking maps;
- lattice spacings tending to zero;
- physical volumes tending to infinity;
- a coupling trajectory;
- a proper compactness functional;
- a coercive pointwise or moment estimate.

From these inputs it derives:

- uniform moments;
- Markov tail estimates;
- compact containment;
- tightness;
- a Prokhorov subsequence;
- a `PhysicalFourDimensionalYangMillsWeakLimit`;
- convergence of bounded-continuous expectations.

Under compatible actions and interpolation equivariance, it transfers gauge invariance, translation invariance, invariant observable laws, n-point expectation convergence, and weak-star convergence of gauge-invariant states.

The physical carrier, interpolation maps, compactness estimates, scaling data, and nontriviality theorem are not generated automatically.

## 6. Continuum time and reflection interfaces

The source includes the dense temporal approximation pattern

```text
latticeTime(n,k) = k * latticeSpacing(n)
  + latticeSpacing(n) -> 0
  -> floor-based approximation of real times.
```

Joint continuity and exact lattice-time invariance then yield continuum real-parameter time invariance.

The selected physical model must still instantiate:

- the continuum time action;
- joint continuity;
- interpolation equivariance;
- gauge/time commutation;
- continuum reflection;
- reflection/time inversion;
- positive-time observable preservation;
- identification of the OS state with the continuum weak-limit state.

## 7. OS Hilbert space and self-adjoint Hamiltonian

From supplied reflection-positive state, covariance, contraction, symmetry, and continuity data, the merged source constructs:

```text
positive-time gauge-invariant observable algebra
  -> OS bilinear form
  -> null submodule
  -> quotient pre-Hilbert space
  -> real Hilbert completion
  -> normalized vacuum
  -> dense physical-state map
  -> contraction semigroup
  -> strong continuity
  -> right generator and Hamiltonian
  -> graph closure
  -> nonnegative self-adjoint closed Hamiltonian.
```

It also constructs shift-resolvent packages, coercive lower bounds, closed-range statements, and vacuum-orthogonal restrictions under the stated hypotheses.

These are theorem-generated consequences of explicit OS data. The complete physical construction of those data remains open.

## 8. Conditional mass-gap transfer on `main`

The direct finite-side certificate stores a positive `mass` and requires a scale-uniform estimate of the form

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2.
```

Equivalent factorized transfer-operator norm interfaces are also present.

Given such a certificate, centered state convergence, reflection positivity, and observable-state strong continuity, the theory derives:

```text
finite boundary contraction
  -> continuum OS quadratic gap
  -> vacuum-orthogonal Hamiltonian Rayleigh lower bound
  -> lower real spectral enclosure
  -> real resolvent interval and norm bound
  -> zero-energy eigenspace equal to the vacuum line
  -> exclusion of nonzero sub-gap eigenvectors.
```

For Hamiltonian-domain vectors orthogonal to the vacuum, the conditional theorem has the form

```text
mass * ||psi||^2 <= <H psi, psi>.
```

The scale-uniform positive certificate is not proved for the intended physical Yang--Mills approximation family.

Therefore the positive `mass` is not yet derived from Wilson dynamics along a complete physical scaling trajectory.

## 9. Exact `33/20` separation

The repository contains an internal normalized theorem and audit lane using

```text
33 / 20.
```

That lane transports the value through internal Hamiltonian, PVM, spectral, and release interfaces.

It is separate from the conditional Wilson/OS `mass` parameter.

No theorem on `main` identifies `33/20` with a physically derived four-dimensional Yang--Mills mass gap.

See `docs/exact_gap_layer_separation.md`.

## Stacked proof frontier

## 10. Explicit periodic oriented `Z2` theorem

PR #302 adds an explicit finite periodic oriented `Z2` small-coupling package with the sufficient condition

```text
beta < log (19 / 17) / 2.
```

It also develops an exponent-two unsigned proxy and transports the coefficient estimate to finite random-scan, Poincare, and heat-bath Hamiltonian consequences.

This remains a finite periodic `Z2` theorem, not an `SU(N)` continuum result.

## 11. Native compact Haar heat-bath `L2` theory

PRs #303--#309 construct:

- canonical one-link Haar coordinates and reconstruction;
- exact one-link Gibbs conditional measures;
- joint density and fiber integral formulas;
- stationarity and reversibility;
- conditional-expectation projection on `L2`;
- idempotence and orthogonal fluctuation decomposition;
- random-scan positive contraction;
- vacuum and vacuum-orthogonal sectors;
- Dobrushin Poincare inequalities;
- heat-bath Hamiltonian and restricted energy operator;
- coercive shifts and Lax--Milgram inverses;
- uniform real resolvent and inverse-norm estimates;
- lower real spectral enclosures;
- a bundled uniform compact Wilson finite-volume spectral certificate.

The stack resolved concrete mathlib issues involving singleton subtype `Fintype` instances, selected-link and off-link Haar products, probability and sigma-finiteness instances, and joint-fiber measurability.

Those replay details do not discharge the physical scale-uniform gap assumption.

## 12. Coercive strong-limit transport

PRs #310--#316 prove:

```text
uniform quadratic coercivity
  + strong operator convergence
  -> coercivity of the limit
  -> norm lower bound and injectivity
  + symmetry
  -> coercive bilinear form
  -> Lax--Milgram inverse
  -> all real shifts below the gap invertible
  -> lower real spectral enclosure
  -> inverse-distance resolvent norm estimate.
```

The construction is then extended from exact Hilbert identifications to approximation maps and isometric embeddings between varying finite-volume Hilbert spaces and a common carrier.

Compact-Wilson wrappers apply the generic theorem to uniform Dobrushin families.

The approximation maps and common-carrier convergence remain hypotheses until a physical interpolation theorem supplies them.

## 13. OS semigroup-defect spectrum

PRs #317--#321 restrict the physical semigroup to the complete vacuum-orthogonal Hilbert sector.

They study

```text
I - T(t)
```

and the rescaled bounded defects

```text
t^(-1) * (I - T(t)).
```

A supplied positive mass slope gives a strict positive-time defect and then the eventual linear estimate

```text
1 - decayFactor(t) >= (mass / 2) * t
```

for sufficiently small positive `t`.

The rescaled defects therefore have a common half-mass coercive lower bound, lower real spectral enclosure, fixed resolvent half-line, and uniform inverse-distance norm control.

This layer consumes the positive mass slope. It does not derive it from Wilson dynamics.

## 14. Hamiltonian core and core-resolvent convergence

PR #322 defines the canonical vacuum-orthogonal right-Hamiltonian core and proves convergence of the rescaled defects to the graph-closed excitation Hamiltonian on each core vector.

PR #323 proves the exact core resolvent-error identity and uniform estimate, yielding resolvent convergence on shifted core inputs.

PR #324 proves that uniformly bounded continuous linear maps converging pointwise on the range of a dense map converge pointwise on the whole normed source space.

PR #325 extracts a reusable vacuum-orthogonal graph-core approximation theorem.

PR #326 proves dense range of the canonical Hamiltonian core shift for every real shift below the relevant gap.

## 15. Full OS strong-resolvent convergence

PR #328 combines the preceding ingredients.

The changed files are:

```text
PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCoreGraphApproximation.lean
PhysicalYangMillsGaugeInvariantOSCoreShiftDenseRange.lean
PhysicalYangMillsGaugeInvariantOSFullStrongResolvent.lean
```

For every

```text
lambda < mass / 2
```

and every excitation vector `y`, it proves

```text
R_tau(lambda) y -> R(lambda) y
```

where `R_tau(lambda)` is the bounded resolvent of the admissible rescaled semigroup defect and `R(lambda)` is the real resolvent of the graph-closed continuum vacuum-orthogonal Hamiltonian.

It also proves

```text
||R_tau(lambda) y - R(lambda) y|| -> 0.
```

The proof architecture is:

```text
full Hamiltonian mass bound
  -> common half-mass Hamiltonian bound
  -> graph-closed continuum resolvent
  -> exact inverse identity on canonical core shifts
  -> dense range of the core shift
  -> uniform resolvent norm bound
  -> pointwise convergence on the dense range
  -> uniformly bounded dense-range extension
  -> full strong-resolvent convergence.
```

This is the present formal frontier.

It remains conditional on:

- a positive `VacuumSemigroupGapSlope`;
- normalized OS data;
- physical semigroup inner symmetry;
- self-adjointness of the graph-closed right Hamiltonian;
- the preceding continuum OS construction;
- the physical approximation data needed to generate those objects.

It is not on `main` at this snapshot.

## Current unresolved obligations

### Repository integration

- rebase the frontier onto current `main`;
- reconcile independently evolved or duplicated files;
- split generic functional analysis from Wilson-specific applications;
- split finite compact heat-bath theory from continuum OS theory;
- obtain ordinary green CI for every unit;
- merge in dependency order;
- refresh theorem indexes after each mathematical integration.

### Physical continuum construction

- choose the gauge-compatible continuum carrier;
- define explicit interpolation or blocking maps;
- specify lattice spacing, physical volume, and coupling trajectories;
- prove compactness and tightness for the actual family;
- prove nontriviality of the weak limit;
- identify gauge quotient or gauge fixing;
- instantiate continuum time and reflection actions;
- identify the continuum observable state.

### Positive physical gap

- prove a scale-uniform positive Dobrushin, Poincare, transfer, block, multiscale, or renormalization-group estimate for the actual physical family;
- distinguish heat-bath Markov time from Euclidean physical time;
- connect the finite spectral certificate to the physical continuum mass slope without assuming the desired positivity;
- preserve the lower bound through the selected continuum limit theorem.

### Reconstruction and physical interpretation

- prove the remaining OS axioms for the concrete continuum theory;
- construct the required Schwinger and Wightman distributions;
- prove clustering and the required uniqueness statements;
- construct local gauge-invariant operator algebras;
- connect the Hamiltonian spectrum to physical observables and units;
- derive any numerical mass value from the instantiated theory.

## Theorem-status table

| Surface | Status |
|---|---|
| Finite compact Wilson Haar--Gibbs measure | proved on `main` |
| Finite `SU(N)` Wilson action bounds and symmetries | proved on `main` |
| Finite even-periodic Wilson reflection positivity | proved on `main` |
| Orientation-correct exact conditional law | proved on `main` |
| Canonical oriented Dobrushin coefficient | proved on `main` |
| Finite heat-bath Hamiltonian gap from `alpha < 1` | proved on `main` |
| Compact finite-volume spectral consequences under strict coefficient | proved on `main` |
| Explicit periodic oriented `Z2` threshold | PR #302, not on `main` |
| Native compact Haar heat-bath `L2` projection | stacked frontier |
| Uniform compact Wilson spectral-gap certificate | stacked frontier |
| Coercive varying-Hilbert strong-limit transport | stacked frontier |
| OS defect and rescaled-defect spectral gaps | stacked frontier |
| Hamiltonian core convergence | stacked frontier |
| Full OS strong-resolvent convergence | PR #328, CI pending at snapshot |
| Concrete physical carrier and interpolation | open |
| Physical scaling and coupling trajectory | open |
| Nontrivial continuum Yang--Mills weak limit | open |
| Scale-uniform positive physical mass estimate | open |
| Fully instantiated OS/Wightman reconstruction | open |
| Physical identification of `33/20` | not established |
| External consensus | not claimed |

## Claim language

Accurate formulations:

- “Lean proves the stated finite-volume Wilson and Dobrushin theorems on `main`.”
- “Lean proves conditional continuum weak-limit, OS Hamiltonian, and mass-gap transfer theorems from explicit hypotheses.”
- “The stacked frontier proves full strong-resolvent convergence from the supplied positive mass-slope and OS hypotheses.”
- “The physical construction and uniform positive gap hypotheses remain open.”

Inaccurate formulations at the current state:

- “The four-dimensional Yang--Mills existence and mass-gap problem is solved.”
- “A nontrivial continuum `SU(N)` theory has been constructed unconditionally.”
- “The physical mass gap has been derived from Wilson dynamics.”
- “The value `33/20` is the derived physical Yang--Mills mass gap.”
- “A stacked-branch merge means the theorem is on `main`.”

## Replay meaning

A successful `lake build` or changed-file CI run establishes that the encoded theorem statements elaborate and their proofs replay in the pinned environment.

It does not establish that:

- the hypotheses correspond to the intended physical Yang--Mills model;
- a conditional theorem has had its hypotheses discharged;
- the mathematical community has independently audited the argument;
- a Clay Millennium Prize claim has been accepted.

Those distinctions remain mandatory in all public status descriptions.
