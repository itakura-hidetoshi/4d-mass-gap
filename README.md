# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-28

This repository is a replayable formal-development and internal-review surface.

It does **not** yet establish an unconditional interacting four-dimensional continuum Yang--Mills theory, a fully instantiated physical Osterwalder--Schrader reconstruction, or an independently derived physical mass gap.

The current development has two complementary lanes.

```text
main
  finite Wilson Gibbs laws
    -> exact single-link conditionals and projections
    -> Gibbs Hilbert space and heat-bath Hamiltonian
    -> canonical Dobrushin-to-Rayleigh theorem
    -> plaquette-local influence bounds
    -> periodic oriented four-dimensional geometry
    -> orientation-correct exact conditional law
    -> local/remote cancellation and normalized-exponential form
    -> oriented conditional-TV and canonical influence bounds

open PR #282
  periodic SU(N) Haar--Gibbs probability laws
    -> gauge and translation invariance
    -> concrete finite even-periodic reflection positivity
    -> conditional physical weak limits
    -> gauge-invariant observables and weak-star states
    -> OS pre-Hilbert quotient and Hilbert completion
    -> positive-time contraction semigroup
    -> closed nonnegative self-adjoint OS Hamiltonian
    -> conditional finite-boundary-to-continuum mass-gap transfer
```

Open-PR results are not statements about `main` until they are merged and replayed there.

## Repository snapshot

```text
latest mathematical proof checkpoint on main:
  923d47c997a9b1b59cfb6a87adc30fdc4fdeee9d
latest merged proof PR:
  PR #298
active physical branch:
  PR #282
PR #282 head:
  509cfbe825ee635940b9fe5728fe1d437a376356
stacked operator-state branch:
  PR #299
```

PR #282 is open and currently reported as mergeable, with 1,315 commits, 334 changed files, and `+42411/-0` relative to `main` at this snapshot.

Its current-head workflows are queued:

- **PR Lean Fast Check**, run 4698;
- **Temporary Concrete Wilson OS Boundary Gap Check**, run 113;
- **Temporary Exponential Boundary Poincare Check**, run 30.

The branch is not treated as merge-ready while ordinary CI is unresolved and temporary diagnostic workflows remain.

## Proved or constructed on `main`

### Finite Gibbs, projection, and Hamiltonian structure

The merged finite-volume source constructs:

```text
finite Wilson action and Gibbs PMF
  -> exact single-link conditional PMF
  -> conditional expectation P_e
  -> fluctuation projection Q_e = I - P_e
  -> detailed balance and Gibbs symmetry
  -> weighted orthogonality and Pythagoras
  -> concrete Gibbs Hilbert space
  -> H_HB = sum_e Q_e
  -> <H_HB f, f> = heat-bath Dirichlet energy
  -> H_HB = |E| (I - P_scan).
```

The vacuum, centered sector, quadratic form, and finite Hamiltonian normalization are explicit Lean objects.

### Canonical Dobrushin-to-Rayleigh theorem

The legacy finite interface proves:

```text
exact conditional-TV influence
  -> canonical coefficient alpha_can
  -> variation and random-scan contraction
  -> centered fixed-point triviality
  -> nonconstant eigenvalue control
  -> Gibbs-Hilbert spectral lift
  -> centered Rayleigh contraction
  -> finite heat-bath Hamiltonian gap.
```

Thus, once `alpha_can < 1` is supplied for a finite system or approximation family, the centered `L2`/Rayleigh and finite Hamiltonian consequences are generated.

### Plaquette support and periodic four-dimensional geometry

The source proves exact localization of Wilson conditional influence to shared plaquettes and the estimate

```text
alpha_can <= d_active * eta_active,

eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

For the signed periodic four-dimensional hypercubic geometry with side length `n >= 3`, it proves

```text
d_active <= 18,
m_shared <= 1.
```

The restriction `n >= 3` is essential because periodic side length two can identify otherwise distinct plaquette incidences.

### Orientation-correct conditional and influence lane

Merged PRs #289 and #293--#298 now provide the physical-link oriented route:

```text
physical-link replacement
  -> agreement away from the replaced source
  -> signed plaquette locality
  -> target-local / target-remote action decomposition
  -> exact oriented single-link conditional PMF
  -> local/remote Boltzmann factorization
  -> exact cancellation of the remote factor
  -> finiteNormalizedExp representation
  -> conditional-TV bound from local action oscillation
  -> exact oriented canonical influence
  -> nonnegativity and exact zero diagonal
  -> sharp active-influence exponential-ratio bound.
```

The next merged finite task is to construct the oriented row sums and canonical coefficient, prove the required off-support zero statements at the coefficient level, and connect this interface directly to the existing Dobrushin/Rayleigh/Hamiltonian API.

## What open PR #282 currently constructs

### Periodic `SU(N)` probability laws and symmetries

The branch uses one variable per positive physical link and inverse values for backward plaquette traversal.

It constructs normalized product-Haar and Wilson Gibbs probability measures, finite gauge invariance, arbitrary periodic translation invariance, and concrete integer temporal translations.

For the periodic four-dimensional lattice it proves

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4.
```

For the standard `SU(N)` Wilson plaquette energy

```text
E_W(U) = 1 - Re(trace U) / N,
```

it proves continuity, conjugation invariance, inversion compatibility, and

```text
0 <= E_W(U) <= 2.
```

### Conditional physical weak-limit route

A common-carrier embedding packages actual finite lattice laws, measurable interpolation, lattice spacing tending to zero, and physical volume tending to infinity.

Given a proper physical functional and a coercive interpolation estimate, the branch generates moment control, compact containment, tightness, a Prokhorov subsequence, and a physical weak-limit package.

This remains conditional on the selected physical carrier, interpolation or blocking maps, proper functional, coercive estimate, and coupling/scaling trajectory.

### Concrete finite reflection positivity

The branch now goes beyond the earlier abstract boundary-fibered certificate.

It contains exact even-periodic reflection geometry, boundary/open-half coordinates, Haar factorization, Wilson Gibbs density factorization, temporal and spatial crossing-sector analysis, local Wilson kernels, and bounded-continuous finite Gibbs reflection positivity.

The main finite theorem is exposed through the periodic even-lattice Wilson reflection-positive surface.

### OS Hilbert space and Hamiltonian

From the supplied continuum reflection-positive state, time-translation, covariance, and continuity data, the branch constructs:

```text
positive-time gauge-invariant observable algebra
  -> OS bilinear form and null quotient
  -> real pre-Hilbert space and Hilbert completion
  -> normalized vacuum and dense state map
  -> contraction semigroup
  -> strong continuity
  -> right generator and right Hamiltonian
  -> graph closure
  -> nonnegativity and positive-shift resolvent
  -> self-adjointness from reflection/time-translation symmetry.
```

The discrete-to-continuum time layer now includes dense floor approximation from `k * latticeSpacing n` and a joint-continuity constructor.

It still requires model-specific physical action, interpolation equivariance, observable restriction, reflection exchange, state identification, and strong-continuity inputs.

### Conditional continuum mass-gap closure

The newest branch theorem chain is explicit about its decisive quantitative hypothesis.

It assumes a scale-uniform finite Wilson shared-boundary estimate of the form

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2,

mass > 0.
```

An equivalent measurable feature-factorization/operator-norm estimate may be used instead.

From that certificate, centered weak-star convergence, and continuum observable-state strong continuity, Mathlib derives:

- a self-adjoint graph-closed continuum OS Hamiltonian;
- the vacuum-orthogonal Rayleigh lower bound with exact mass `mass`;
- identification of the zero-energy eigenspace with the normalized vacuum line;
- exclusion of nonzero eigenvectors with energy in `(0, mass)`.

This is a conditional gap-transfer theorem.

The repository does **not** yet prove the required scale-uniform strict Wilson boundary estimate for the physical approximation family.

### PR #299

PR #299 is stacked on the physical branch and constructs the vacuum vector functional

```text
omega_Omega(T) = <Omega, T Omega>
```

on bounded real-linear operators, with linearity, normalization, and positivity on the Hilbert quadratic positive cone.

It is not on `main`, and it does not yet construct a local von Neumann algebra, standard form, type-III classification, or modular theory.

## Current theorem boundary

| Surface | Current status |
|---|---|
| Finite Wilson Gibbs, projections, Gibbs Hilbert space | proved on `main` |
| Canonical heat-bath Hamiltonian | proved on `main` |
| Legacy canonical Dobrushin-to-Rayleigh and finite-gap theorem | proved on `main` |
| Periodic four-dimensional incidence bounds | proved on `main` for `n >= 3` |
| Oriented exact conditional, remote cancellation, normalized exponential | proved on `main` |
| Oriented exact canonical influence and active bound | proved on `main` |
| Oriented row-sum coefficient and direct Hamiltonian bridge | open |
| Explicit periodic `Z2` strict-parameter theorem | open |
| Periodic `SU(N)` Haar--Gibbs and finite reflection positivity | implemented in PR #282 |
| Physical weak limit | conditional in PR #282 |
| OS Hilbert completion and self-adjoint Hamiltonian | conditional in PR #282 |
| Positive continuum mass-gap transfer | conditional in PR #282 on a strict boundary estimate |
| Scale-uniform strict Wilson boundary estimate | open |
| Concrete physical carrier, scaling, and coercive compactness | open |
| Nontrivial interacting continuum theory | open |
| Full OS/Wightman reconstruction | open |
| Independent physical derivation of `33/20` | open |
| External mathematical consensus | not claimed |

## Exact `33/20` lane

The repository transports the normalized value `33/20` through internal Hamiltonian, PVM, spectral, and audit interfaces.

This is an internal normalization and dependency-routing surface.

It is **not** an independent derivation of the physical four-dimensional Yang--Mills mass gap and is not identified with the conditional mass parameter in PR #282.

See `docs/exact_gap_layer_separation.md`.

## Primary review anchors

| Topic | File |
|---|---|
| Authoritative status | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Oriented conditional law | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonSingleLinkConditional.lean` |
| Oriented remote cancellation | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonConditionalRemoteCancellation.lean` |
| Oriented canonical influence | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence.lean` |
| Oriented influence bound | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonCanonicalInfluenceBound.lean` |
| Physical weak-limit constructor | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryWeakLimit.lean` in PR #282 |
| Finite Wilson reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsReflectionPositivity.lean` in PR #282 |
| OS Hamiltonian spine | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean` in PR #282 |
| Boundary-gap frontier | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSBoundaryGapFrontierSpine.lean` in PR #282 |
| Conditional gap closure | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryGapClosure.lean` in PR #282 |
| Exact-gap separation | `docs/exact_gap_layer_separation.md` |

## Replay

Pinned toolchain:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
lake build
```

A successful replay verifies the declared Lean source in the pinned environment.

It is reproducibility evidence, not external certification of the physical theorem.

## Current priorities

1. Complete the oriented row-sum/coefficient layer and connect it to the merged Dobrushin/Rayleigh/Hamiltonian spine.
2. State the explicit periodic `Z2` finite strict-parameter theorem.
3. Stabilize PR #282 with ordinary CI, remove temporary workflows, and split the branch into reviewable merge units.
4. Prove the scale-uniform strict Wilson shared-boundary estimate or an equivalent factorized operator-norm estimate.
5. Instantiate the physical carrier, interpolation, coupling trajectory, temporal/reflection covariance, and strong-continuity data.
6. Prove nontriviality, interacting character, remaining OS axioms, and the physical reconstruction.
7. Derive physical normalization and any numerical mass value independently of the internal `33/20` lane.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for the four-dimensional
Yang--Mills existence and mass-gap problem. The main branch proves a substantial
finite Wilson Gibbs, heat-bath Hamiltonian, Dobrushin-to-Rayleigh, periodic
four-dimensional geometry, and orientation-correct conditional-influence spine.
Open PR #282 additionally constructs periodic SU(N) Haar--Gibbs laws, concrete
finite reflection positivity, conditional continuum weak limits, an OS Hilbert
and Hamiltonian route, and a theorem transferring a supplied scale-uniform
boundary Poincare estimate to a positive continuum Hamiltonian gap. The decisive
scale-uniform physical estimate, the final carrier and scaling construction,
nontriviality, full reconstruction, and an independent numerical mass-gap
derivation remain open.
```
