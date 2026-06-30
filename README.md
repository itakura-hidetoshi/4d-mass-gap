# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Authoritative proof status: docs/current_proof_status.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-06-30

This repository is a replayable formal-development surface.

It does **not** yet establish an unconditional interacting four-dimensional continuum Yang--Mills theory, a fully instantiated physical Osterwalder--Schrader reconstruction, or a physical mass gap derived from a concrete continuum scaling trajectory.

The current source must be read in two layers.

```text
main
  merged finite Wilson and Dobrushin mathematics
  merged finite SU(N) Haar--Gibbs and reflection-positive theory
  merged conditional weak-limit, OS Hilbert, Hamiltonian, and gap-transfer constructors

stacked proof frontier
  native compact-group heat-bath L2 theory
  uniform finite-volume spectral certificates
  coercive strong-limit transport across varying Hilbert spaces
  OS semigroup-defect spectral gaps
  graph-core and full strong-resolvent convergence
```

A result on the stacked proof frontier is not a result on `main` until the corresponding branch has been rebased, reviewed, merged into `main`, and replayed there.

Likewise, a theorem that accepts a positive mass slope, a uniform Dobrushin bound, a coercive compactness estimate, or a physical interpolation package as input is a conditional theorem. It does not prove that the physical four-dimensional Wilson family supplies that input.

## Repository snapshot

```text
main head:
  a80a75449a16d07889519c1823595c5244824583

latest merged main proof PR:
  PR #300 — oriented canonical Dobrushin coefficient and compact Wilson gap lane

large physical construction merged into main:
  PR #282
  merge commit ed42e5af631aec11f16c7095c3cd892b488bd04d

current stacked frontier:
  PR #328 — Prove full OS strong-resolvent convergence
  head 540cc5848626fce2a69fff6948e14886e9591277
  base formal/real-hilbert-uniform-coercive-strong-limit
  base commit a846a06aa286f4d0beb624bfd5e461653b797b58
```

At this snapshot, PR #328 is open, non-draft, and reported as mergeable. Its **PR Lean Fast Check** run 5141 is in progress.

The frontier branch and `main` have diverged. Relative to `main`, the PR #328 head is reported as 237 commits ahead and 157 commits behind, with merge base `929e20583ae368475d4bedb65c060c2d3c4c0fff`. The frontier therefore requires deliberate rebase and decomposition before it can become the next `main` state.

## What is proved on `main`

### Finite Wilson probability, reflection, and OS input theory

The merged source contains a concrete finite periodic compact-gauge Wilson theory with:

```text
positive physical links
  -> normalized product Haar measure
  -> Wilson Gibbs probability measure
  -> finite gauge and translation invariance
  -> even-periodic reflection geometry
  -> boundary/open-half Haar factorization
  -> Wilson Gibbs density factorization
  -> local positive-semidefinite crossing kernels
  -> finite Gibbs reflection positivity.
```

The `SU(N)` specialization includes the standard Wilson plaquette energy

```text
E_W(U) = 1 - Re(trace U) / N
```

with continuity, conjugation invariance, inversion compatibility, and the bound

```text
0 <= E_W(U) <= 2.
```

These are finite-volume theorems. They are not by themselves a continuum existence theorem.

### Orientation-correct Dobrushin and heat-bath theory

The merged orientation-correct lane now contains:

```text
exact single-link conditional law
  -> target-local / target-remote action decomposition
  -> exact remote-factor cancellation
  -> exact conditional total-variation influence
  -> plaquette-support locality
  -> exact row sums and canonical Dobrushin coefficient
  -> Dobrushin matrix and variation contraction
  -> random-scan contraction
  -> Gibbs Hilbert realization
  -> Rayleigh and Poincare inequalities
  -> normalized heat-bath Hamiltonian gap.
```

For four-dimensional periodic geometry with side length at least three, the source formalizes the local incidence bounds used by the coefficient estimate, including the active-neighbor bound `18` and the one-shared-plaquette bound.

The compact-group lane also packages the strict hypothesis `alpha < 1` into finite-volume vacuum-sector spectral, coercive, and resolvent consequences.

This closes the **finite theorem generator** from a strict Dobrushin coefficient to a finite heat-bath Hamiltonian gap.

It does not prove that a physically renormalized continuum approximation family satisfies a scale-uniform strict Dobrushin condition.

### Conditional physical weak limits

The merged physical construction provides a common-carrier framework for finite periodic Wilson measures.

Given explicit interpolation or blocking maps, lattice spacing and volume data, a proper compactness functional, and a coercive moment estimate, the source derives:

- uniform moment and tail control;
- compact containment and tightness;
- a Prokhorov subsequence;
- bounded-continuous expectation convergence;
- gauge and translation invariance of the limit under the required equivariance hypotheses.

The physical carrier, scaling trajectory, coupling renormalization, compactness functional, coercive estimate, and nontriviality proof remain model-specific inputs.

### OS Hilbert space and Hamiltonian constructors

From a continuum reflection-positive state with the required time-covariance and continuity data, the merged source constructs:

```text
positive-time gauge-invariant observables
  -> OS bilinear form
  -> null quotient
  -> real pre-Hilbert space
  -> Hilbert completion
  -> normalized vacuum
  -> strongly continuous contraction semigroup
  -> right generator and right Hamiltonian
  -> graph closure
  -> nonnegative self-adjoint Hamiltonian
  -> real resolvent estimates.
```

This is a formal reconstruction package from explicit hypotheses. The repository does not yet instantiate every hypothesis from one concrete nontrivial continuum Yang--Mills measure.

### Conditional continuum mass-gap transfer

The merged source contains conditional transfer theorems of the following form.

A positive scale-uniform finite-side estimate or equivalent transfer-operator contraction certificate is supplied:

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2,

mass > 0.
```

Together with the continuum state and OS continuity package, the formal theory derives:

- a vacuum-orthogonal Hamiltonian Rayleigh lower bound;
- a lower real spectral enclosure;
- a resolvent half-line and inverse-distance norm estimates;
- identification of the zero-energy eigenspace with the vacuum line;
- exclusion of nonzero eigenvectors below the supplied positive mass.

The required physical scale-uniform strict estimate is not yet derived from the actual four-dimensional continuum scaling trajectory.

## Current stacked proof frontier

The post-`main` development is organized as a stacked sequence.

### Finite explicit and native compact heat-bath layers

PR #302 packages an explicit periodic oriented `Z2` small-coupling theorem, including the sufficient condition

```text
beta < log (19 / 17) / 2.
```

PRs #303--#309 construct the native compact-group one-link Haar heat-bath kernel, its `L2` conditional-expectation projection, reversibility, Poincare and Hamiltonian structures, uniform Dobrushin resolvents, lower spectral enclosures, and a bundled uniform finite-volume spectral-gap certificate.

These are finite-volume or uniform-family results. The uniform family hypotheses are not yet proved along the physical continuum Yang--Mills trajectory.

### Strong-limit transport

PRs #310--#316 prove that a uniform coercive symmetric gap can pass to a common Hilbert carrier under increasingly flexible identifications:

```text
identified strong limit
  -> coercivity and symmetry of the limit
  -> Lax--Milgram invertibility
  -> shifted resolvents and lower spectral enclosure
  -> asymptotic isometric embeddings
  -> compact Wilson specialization.
```

This separates the functional-analytic transport theorem from the physical construction of the approximation maps.

### OS defect spectrum and Hamiltonian limit

PRs #317--#321 restrict the physical semigroup to the vacuum-orthogonal Hilbert sector and prove spectral bounds for

```text
I - T(t)
```

and for the rescaled defects

```text
t^(-1) (I - T(t)).
```

A positive continuum mass slope yields a sufficiently small positive-time defect gap, then a time-independent half-mass coercive bound for the rescaled defects.

PRs #322--#324 prove convergence on the canonical Hamiltonian core, convergence of the corresponding resolvents on the core-shift range, and the generic extension of uniformly bounded pointwise limits from a dense range to the full Hilbert space.

PRs #325 and #326 isolate the vacuum-orthogonal graph-core approximation and dense core-shift range theorems.

PR #328 combines these ingredients and proves full strong-resolvent convergence at every real shift

```text
lambda < mass / 2
```

from the bounded rescaled semigroup-defect resolvents to the graph-closed continuum excitation-Hamiltonian resolvent, on every vector in the excitation Hilbert space.

This is the present formal frontier. It remains conditional on the previously supplied positive mass slope, OS semigroup package, self-adjointness, and the physical approximation data that generate those structures.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite compact Wilson Haar--Gibbs probability theory | proved on `main` |
| Finite even-periodic Wilson reflection positivity | proved on `main` |
| Orientation-correct canonical Dobrushin coefficient | proved on `main` |
| Finite random-scan, Poincare, and heat-bath Hamiltonian gap from `alpha < 1` | proved on `main` |
| Explicit periodic oriented `Z2` threshold theorem | implemented in PR #302, not on `main` |
| Native compact Haar heat-bath `L2` projection and Hamiltonian | stacked frontier |
| Uniform compact Wilson finite-volume spectral certificate | stacked frontier |
| Coercive strong-limit and varying-Hilbert transport | stacked frontier |
| Full OS strong-resolvent convergence | implemented in PR #328, CI pending at this snapshot |
| Concrete gauge-compatible continuum carrier and interpolation | open |
| Renormalized coupling and scaling trajectory | open |
| Uniform positive gap for the physical approximation family | open |
| Nontrivial interacting continuum limit | open |
| Full instantiated OS/Wightman reconstruction | open |
| Physical numerical mass value and units | open |
| Independent external mathematical consensus | not claimed |

## Exact `33/20` lane

The repository transports the normalized value `33/20` through internal Hamiltonian, spectral, and audit interfaces.

This is an internal normalization and dependency-routing surface.

It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap, and it is not identified with the conditional `mass` parameter used by the Wilson/OS transfer theorems.

See `docs/exact_gap_layer_separation.md`.

## Primary review anchors

| Topic | File |
|---|---|
| Authoritative proof status | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Finite Wilson reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsReflectionPositivity.lean` |
| Oriented Dobrushin coefficient | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient.lean` |
| Four-dimensional compact Wilson certificate | `MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonFourDimensionalDobrushinCertificate.lean` |
| Finite heat-bath Hamiltonian gap | `MGAP4D/MathlibAnalytic/FiniteOrientedWilsonCanonicalDobrushinHamiltonianGap.lean` |
| Physical weak-limit constructor | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryWeakLimit.lean` |
| OS Hamiltonian spine | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean` |
| Conditional boundary-gap closure | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryGapClosure.lean` |
| Frontier full strong resolvent | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSFullStrongResolvent.lean` in PR #328 |
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

A successful replay verifies the declared Lean source in the pinned environment. It is reproducibility evidence, not external certification of the physical theorem.

## Immediate priorities

1. Finish CI for PR #328 and record the exact replay receipt.
2. Rebase the stacked frontier onto `main` and split it into reviewable merge units.
3. Merge the explicit finite `Z2`, native compact Haar heat-bath, uniform spectral, strong-limit, and strong-resolvent layers in dependency order.
4. Instantiate one concrete gauge-compatible continuum carrier, interpolation scheme, scaling trajectory, and nontriviality argument.
5. Prove a scale-uniform positive gap estimate for that actual physical approximation family.
6. Apply the merged OS Hamiltonian and strong-resolvent machinery to the instantiated continuum model.
7. Complete the remaining OS/Wightman, physical-normalization, and external-review obligations.

## License and attribution

Copyright belongs to Hidetoshi Itakura except where third-party licenses apply.

See the repository license files and individual source headers for exact terms.
