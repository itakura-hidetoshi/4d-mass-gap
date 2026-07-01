# Current proof status

**Updated:** 2026-07-01  
**Latest mathematical proof checkpoint on `main`:** `a80a75449a16d07889519c1823595c5244824583`  
**Latest merged mathematical proof PR on `main`:** PR #300  
**Current `main` documentation head:** `e20a26cc3034c2e5c793d371b034585ab57cc385`  
**Active proof carrier:** `formal/real-hilbert-uniform-coercive-strong-limit`, `7f1dae659bef10ea1713d57d20a620d1065fbf1d`  
**Latest integrated proof PR on the carrier:** PR #364  
**Latest carrier CI:** PR Lean Fast Check run 5205 succeeded

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
  authoritative merged release surface
  replayable finite Wilson mathematics
  conditional continuum and OS theorem generators

formal/real-hilbert-uniform-coercive-strong-limit
  integrated active proof carrier
  post-main finite L2, strong-limit, OS defect,
  strong-resolvent, and operator-graph development
```

A theorem merged into the active carrier is not thereby merged into `main`.

A theorem whose hypotheses include a positive mass slope, a strict Dobrushin coefficient, a scale-uniform Poincare estimate, a coercive compactness estimate, a physical interpolation package, or self-adjoint OS data remains conditional until those hypotheses are constructed for the intended physical approximation family.

## Repository snapshot

### Authoritative `main` checkpoint

```text
mathematical checkpoint:
  a80a75449a16d07889519c1823595c5244824583

latest mathematical proof PR on main:
  PR #300

current documentation head:
  e20a26cc3034c2e5c793d371b034585ab57cc385

large physical construction merged earlier:
  PR #282
  merge commit ed42e5af631aec11f16c7095c3cd892b488bd04d
```

PR #282 placed the finite `SU(N)`, weak-limit, reflection-positive, OS Hilbert, Hamiltonian, and conditional mass-gap construction on `main`.

PR #300 merged the orientation-correct canonical Dobrushin coefficient, compact Wilson coefficient-to-gap route, and related finite heat-bath and resolvent infrastructure.

Documentation-only commits after the checkpoint do not change the mathematical theorem bodies described below.

### Active proof carrier

```text
branch:
  formal/real-hilbert-uniform-coercive-strong-limit

head:
  7f1dae659bef10ea1713d57d20a620d1065fbf1d

latest integrated proof PR:
  PR #364 — Package canonical strong resolvent and graph convergence

PR #364 source head:
  67428df16f4057b7956f2b873a90c639572d070d

validation:
  PR Lean Fast Check run 5205 — success
```

PR #328's earlier failure in `PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCoreGraphApproximation.lean` has been repaired.

Its final head and validation are:

```text
PR #328 final head:
  ba8b9e09856dd419e577a6861addd8f0893c7b56

PR Lean Fast Check:
  run 5151 — success

merge commit on the carrier:
  c2c5922da6120883b4ad6400cbda8912772e390a
```

The active carrier is therefore replay-clean at its current head.

It has not been promoted to `main`.

Relative to the current `main` documentation head, GitHub reports:

```text
ahead:       359 commits
behind:      169 commits
merge base:  929e20583ae368475d4bedb65c060c2d3c4c0fff
```

The carrier requires deliberate reconciliation, duplicate-file review, and dependency-preserving decomposition before promotion.

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

These finite-volume bounds do not derive the renormalized coupling trajectory of continuum Yang--Mills theory.

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

A finite small-coupling estimate is not automatically uniform along a continuum scaling trajectory.

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

The selected physical model must still instantiate the continuum time action, joint continuity, interpolation equivariance, gauge/time commutation, continuum reflection, reflection/time inversion, positive-time observable preservation, and identification of the OS state with the continuum weak-limit state.

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

These are theorem-generated consequences of explicit OS data.

The complete physical construction of those data remains open.

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

No theorem on `main` or the active carrier identifies `33/20` with a physically derived four-dimensional Yang--Mills mass gap.

See `docs/exact_gap_layer_separation.md`.

## Integrated active proof carrier

## 10. Explicit periodic oriented `Z2` theorem

The active carrier contains an explicit finite periodic oriented `Z2` small-coupling package with the sufficient condition

```text
beta < log (19 / 17) / 2.
```

It also develops an exponent-two unsigned proxy and transports the coefficient estimate to finite random-scan, Poincare, and heat-bath Hamiltonian consequences.

This remains a finite periodic `Z2` theorem, not an `SU(N)` continuum result.

PR #302 remains open against `main` and is not a merged `main` result.

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

The carrier resolves the required singleton-subtype `Fintype`, selected-link and off-link Haar-product, probability, sigma-finiteness, joint-fiber measurability, and conditional-expectation interfaces.

These replay details do not discharge the physical scale-uniform gap assumption.

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

The construction extends from exact Hilbert identifications to approximation maps and isometric embeddings between varying finite-volume Hilbert spaces and a common carrier.

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

This layer consumes the positive mass slope.

It does not derive it from Wilson dynamics.

## 14. Hamiltonian core and full strong-resolvent convergence

PRs #322--#326 define the canonical vacuum-orthogonal right-Hamiltonian core, prove convergence of the rescaled defects on that core, establish exact core resolvent-error identities, extend uniformly bounded pointwise convergence from a dense range, construct graph-core approximations, and prove dense range of the canonical core shift.

PR #328 combines these ingredients.

For every

```text
lambda < mass / 2
```

and every excitation vector `y`, the carrier proves

```text
R_tau(lambda) y -> R(lambda) y,
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

The final PR #328 head passed run 5151 and was merged into the active carrier.

This theorem remains conditional on:

- a positive `VacuumSemigroupGapSlope`;
- normalized OS data;
- physical semigroup inner symmetry;
- self-adjointness of the graph-closed right Hamiltonian;
- the preceding continuum OS construction;
- the physical approximation data needed to generate those objects.

## 15. Resolvent-selected graph convergence

PR #332 upgrades full strong-resolvent convergence to convergence of graph pairs.

For the resolvent-selected solutions, it proves simultaneous convergence of

```text
(R_tau(lambda)y, D_tau R_tau(lambda)y)
```

to

```text
(R(lambda)y, H R(lambda)y).
```

PRs #333--#341 then develop graph approximation of arbitrary continuum Hamiltonian domain points, graph-norm and sum-norm formulations, closure and range characterizations, and sequential closed-graph limits.

These results concern the graph of the closed excitation Hamiltonian generated by the supplied OS data.

They do not construct the physical OS data themselves.

## 16. Approximate and varying shifted-defect graph limits

PRs #342--#349 prove convergence and limit identification for shifted finite-time defect equations.

The formal interfaces allow:

- exact or vanishing residual errors;
- varying right-hand sides;
- varying real shifts converging below `mass / 2`;
- arbitrary nontrivial index filters;
- reconstruction of the canonical continuum resolvent graph point.

The conclusions retain the relevant small-time and below-gap hypotheses.

They do not assert graph convergence for arbitrary finite times or arbitrary shifts.

## 17. Filter Painleve--Kuratowski convergence

PRs #350--#358 define and connect:

- filter-indexed Painleve--Kuratowski outer limits;
- convergent-selection outer limits;
- filter-indexed inner limits;
- recovery nets;
- exact shifted-defect graph families;
- singleton graph representations;
- equivalences between point convergence and singleton inner/outer limits.

PR #359 was a superseded draft and is not part of the authoritative chain.

PR #360 proves full shifted-graph Painleve--Kuratowski convergence while retaining source and shift coordinates.

PR #361 passes to ordinary operator graphs.

It proves that both filter Painleve--Kuratowski limits of the bounded finite-time rescaled-defect graphs equal the graph of the closed continuum excitation Hamiltonian, with the auxiliary below-gap shift used only in the proof.

PR #362 removes the auxiliary shift from the public theorem statement by selecting the constant shift zero internally.

PR #363 proves that the canonical admissible positive small-time filter is nontrivial and supplies the final canonical theorem with no explicit source, shift, time-net, or filter-nontriviality argument exposed to the theorem user.

The canonical conclusion is:

```text
KuratowskiInnerLimit(finite-time defect graphs)
  = graph(H)

KuratowskiOuterLimit(finite-time defect graphs)
  = graph(H)
```

on the admissible positive small-time filter.

This is filter-indexed operator-graph convergence.

It is not a theorem that the unrestricted union of all finite-time graphs has closure equal to `graph(H)`.

## 18. Canonical operator-limit package

PR #364 packages the two principal operator-limit conclusions under common assumptions.

The theorem simultaneously supplies:

```text
for every lambda < mass / 2 and every y:
  R_tau(lambda)y -> R(lambda)y
```

and

```text
both canonical Painleve--Kuratowski graph limits
  = graph of the closed continuum excitation Hamiltonian.
```

The package is exported through both `MGAP4D.MathlibAnalytic` and the root `MGAP4D` import surface on the active carrier.

Its validation receipt is:

```text
PR #364 head:
  67428df16f4057b7956f2b873a90c639572d070d

PR Lean Fast Check:
  run 5205 — success

carrier merge commit:
  7f1dae659bef10ea1713d57d20a620d1065fbf1d
```

The package does not strengthen or discharge the underlying OS, self-adjointness, or mass-slope assumptions.

It does not establish norm-resolvent convergence.

It does not establish convergence of every spectral projection without additional hypotheses.

## Current unresolved obligations

### Repository integration

- reconcile the active carrier with current `main`;
- remove the 169-commit backward divergence;
- reconcile independently evolved or duplicated files;
- split generic functional analysis from Wilson-specific applications;
- split finite compact heat-bath theory from continuum OS theory;
- preserve compile-smoke roots for each merge unit;
- obtain ordinary green CI for every unit;
- merge in dependency order;
- refresh theorem indexes after each mathematical promotion.

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

### Further operator analysis

- identify the hypotheses needed for bounded functional-calculus convergence;
- connect strong-resolvent convergence to semigroup convergence using the appropriate theorem;
- study isolated spectral projections only under sufficient additional assumptions;
- formalize any required Mosco, graph, or form-convergence equivalences;
- avoid inferring norm-resolvent convergence from the current results.

## Theorem-status table

| Surface | Status |
|---|---|
| Finite compact Wilson Haar--Gibbs measure | proved on `main` |
| Finite `SU(N)` Wilson action bounds and symmetries | proved on `main` |
| Finite even-periodic Wilson reflection positivity | proved on `main` |
| Orientation-correct exact conditional law | proved on `main` |
| Canonical oriented Dobrushin coefficient | proved on `main` |
| Finite heat-bath Hamiltonian gap from `alpha < 1` | proved on `main` |
| Conditional physical weak-limit constructor | proved on `main` from explicit hypotheses |
| Conditional OS Hilbert and self-adjoint Hamiltonian | proved on `main` from explicit hypotheses |
| Conditional continuum mass-gap transfer | proved on `main` from a supplied positive certificate |
| Explicit periodic oriented `Z2` threshold | active carrier; PR #302 open against `main` |
| Native compact Haar heat-bath `L2` projection | integrated on active carrier |
| Uniform compact Wilson spectral-gap certificate | integrated on active carrier |
| Coercive varying-Hilbert strong-limit transport | integrated on active carrier |
| OS defect and rescaled-defect spectral gaps | integrated on active carrier |
| Hamiltonian core convergence | integrated on active carrier |
| Full OS strong-resolvent convergence | integrated on active carrier; run 5151 succeeded |
| Resolvent-selected graph convergence | integrated on active carrier |
| Filter Painleve--Kuratowski ordinary graph convergence | integrated on active carrier |
| Canonical operator-limit package | PR #364 integrated on active carrier; run 5205 succeeded |
| Promotion of the active carrier to `main` | not completed |
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
- “Lean proves conditional continuum weak-limit, OS Hamiltonian, and mass-gap transfer theorems from explicit hypotheses on `main`.”
- “The active proof carrier has green Lean replay receipts through the canonical strong-resolvent and operator-graph convergence package.”
- “The canonical operator-limit package remains conditional on the supplied mass-slope, normalized OS, symmetry, and self-adjointness hypotheses.”
- “The physical continuum construction and uniform positive gap remain open.”

Inaccurate formulations at the current state:

- “The four-dimensional Yang--Mills existence and mass-gap problem is solved.”
- “A nontrivial continuum `SU(N)` theory has been constructed unconditionally.”
- “The physical mass gap has been derived from Wilson dynamics.”
- “The value `33/20` is the derived physical Yang--Mills mass gap.”
- “A carrier-branch merge means the theorem is on `main`.”
- “Strong-resolvent convergence implies norm-resolvent convergence.”
- “The current graph theorem identifies the closure of the unrestricted union of all finite-time graphs.”
- “Every spectral projection converges from the current hypotheses.”

## Replay meaning

A successful `lake build` or changed-file CI run establishes that the encoded theorem statements elaborate and their proofs replay in the pinned environment.

It does not establish that:

- the hypotheses correspond to the intended physical Yang--Mills model;
- a conditional theorem has had its hypotheses discharged;
- the active carrier has been reconciled and merged into `main`;
- the mathematical community has independently audited the argument;
- a Clay Millennium Prize claim has been accepted.

Those distinctions remain mandatory in all public status descriptions.
