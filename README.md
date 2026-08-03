# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository develops formal theorem infrastructure and concrete finite-volume Wilson models along several converging routes. It does **not** currently contain an unconditional construction of interacting four-dimensional continuum Yang--Mills theory, and it does **not** claim a proof of the Clay Millennium problem.

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Detailed proof-development plan:
  ROADMAP.md

KuuOS reference bridge:
  docs/kuuos_reference_bridge.md
```

## Authoritative status — 2026-08-03 JST

```text
latest integrated theorem checkpoint:
  PR #1365 — Construct shifted geometric Wilson OS kernel operator semigroup

fixed PR head:
  9d275aee4cfaf8c0a056b8e17c466cbc45b9dee5

authoritative carrier / squash integration:
  4600dc1488a0b80576d247075ce2afdafd48edfa

validation:
  PR Lean Fast Check #8625
  run id 30780128446
  job id 91582993004
  completed / success

terminal build:
  Build completed successfully (8758 jobs)

post-merge comparison:
  4600dc1488a0b80576d247075ce2afdafd48edfa
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Only results merged into the authoritative carrier count as current theorem status. Open, Draft, stale, superseded, or closed-unmerged pull requests are historical or experimental unless their content has subsequently been integrated.

## Executive summary

The formal development now has four distinct but connected lanes.

```text
A. OS reconstruction / PVM / Hamiltonian / exact-spectrum infrastructure

Euclidean and reflection-positive input
  -> OS quotient and real Hilbert completion
  -> strongly continuous semigroup and generator
  -> self-adjoint Hamiltonian interfaces
  -> bounded-Borel PVM calculus and spectral support
  -> exact lower-spectrum consequences from a supplied construction spine


B. finite periodic compact-Haar SU(N) Wilson dynamics

Wilson Gibbs measure and exact one-link conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit Dobrushin influence matrix
  -> genuine centered random-scan Rayleigh input
  -> finite Gibbs L2 Poincare/coercivity and centered exponential decay


C. boundary transfer and finite-to-continuum coercivity

reflection-fixed boundary Haar L2
  -> canonical boundary-to-Gibbs analysis isometry
  -> adjoint synthesis and compressed Hamiltonian
  -> full and centered heat-bath semigroups
  -> reflected-integral / vacuum-decay packages
  -> conditional continuum Hamiltonian coercivity transfer


D. geometric Osterwalder--Schrader transfer

one-layer Wilson reflection form
  -> OS Hilbert completion
  -> identity-transfer uniqueness obstruction
  -> independent shifted geometric kernel certificate
  -> quotient descent and completed positive contraction
  -> discrete natural-time semigroup
  -> exact comparison defects against unshifted and heat-bath dynamics
```

The newest development clarifies a crucial distinction: the unshifted one-layer reflection form is the inner product of its OS completion and therefore realizes only the identity transfer. A nontrivial geometric Euclidean-time operator requires genuinely shifted kernel data. The repository now constructs the operator and its discrete semigroup **from such an independent shifted-kernel certificate**, but it has not yet derived that certificate from a concrete nonzero-coupling four-dimensional Wilson time-translation geometry.

## What is formally integrated

### 1. Exact lower-spectrum consequences from a supplied continuum construction spine

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

the repository derives the exact lower-spectrum package associated with `exactGapValueReal`, including:

```text
vacuum energy at zero
no spectrum in the open interval below the threshold
threshold membership
least nonzero spectral value
infimum characterization of the nonzero spectrum
first-excitation identification
uniqueness of the least nonzero spectral energy.
```

This is a theorem from the fields of the supplied spine. It does not construct the required interacting continuum gauge model.

### 2. Reconstructed real Hilbert space, Hamiltonian, PVM, and bounded-Borel calculus

The integrated OS lane includes:

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
physical semigroup and strong-continuity routes
generator and graph-closure infrastructure
self-adjoint Hamiltonian interfaces
simple-function PVM integration
bounded-Borel operator-norm completion
quadratic scalar spectral measures
polarization and multiplicativity
spectral-support identification.
```

The spectral threshold is characterized through support membership, leastness, and infimum statements. The formal package does not require the threshold to be an isolated eigenvalue unless an additional atom theorem is supplied.

### 3. Explicit periodic compact-Haar `SU(N)` Wilson system

The finite-volume model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar measure. The carrier contains:

```text
finite periodic Wilson Gibbs probability
exact one-link conditional probability laws
one-link heat-bath projections
Gibbs reversibility and Hilbert-space projection structure
native conditional-variance and Dirichlet identities
shared-plaquette localization
explicit bounded-test influence coefficients
periodic active-neighbor counting
symmetric volume-independent Dobrushin matrices.
```

The explicit coefficient package is

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta
```

with the proved strict small-coupling region

```text
beta < log (19 / 17) / 4.
```

This is an explicit finite-volume total-variation / bounded-test influence result. It is not, by itself, an `L²` Rayleigh theorem.

### 4. Finite Gibbs `L²` Poincare, coercivity, and centered heat-bath decay

The repository combines:

```text
an explicit compact-Haar Dobrushin matrix
a genuine centered random-scan Rayleigh certificate
a strict common coefficient bound below one
```

to generate finite and tail-uniform theorem packages for:

```text
Gibbs L2 Poincare inequalities
vacuum-orthogonal heat-bath coercivity
exact characterization of the Gibbs-vacuum kernel
centered heat-bath operator-norm decay
finite reflected-integral decay
conditional continuum coercivity transfer.
```

The centered semigroup estimate has the form

```text
||exp (-(t / 2) H_HB) P_vacuum_perp f||
  <= sqrt (exp (-gap * t)) * ||f||.
```

The distinction between influence control and `L²` control is explicit: the repository does not promote total-variation Dobrushin contraction to an `L²` spectral gap without the required Rayleigh input.

### 5. Canonical boundary Haar-to-Gibbs analysis and adjoint compression

The reflection-fixed boundary carrier is no longer represented by an arbitrary Hilbert-space map. The integrated construction uses:

```text
boundary projection pullback
  -> full-configuration product-Haar L2
  -> multiplication by sqrt(Z) * exp(-S/2)
  -> finite Wilson Gibbs L2.
```

This gives a canonical linear isometry from boundary Haar `L²` to the actual finite Wilson Gibbs `L²` carrier. Its real-Hilbert adjoint supplies canonical synthesis.

The repository then constructs:

```text
compressed boundary Hamiltonian A* H_HB A
compressed full and centered heat-bath evolutions
exact quadratic-form and matrix-coefficient identities
vacuum transport and centering compatibility
generator leakage and second-moment curvature defects
zero-defect all-time semigroup and intertwining theorems.
```

For general nonzero coupling, exact invariance of the analyzed boundary range and exact identification with geometric OS time remain model-specific obligations.

### 6. Complete beta-zero canonical boundary heat-bath package

At the actual finite periodic-even Wilson system with `beta = 0`, the repository proves:

```text
Wilson Gibbs law = product Haar law
boundary marginal = boundary Haar law
canonical boundary analysis = boundary-restriction pullback
one-link heat-bath projections preserve the analyzed range
generator leakage defect = 0
second-moment curvature defect = 0
sharp boundary Poincare/coercivity constant = 1
no nonzero vacuum-orthogonal zero mode
exact all-real-time compressed heat-bath semigroup
ambient/boundary intertwining
operator-norm continuity and derivative formulas.
```

This is a complete finite-volume beta-zero boundary heat-bath result. It does not identify heat-bath Markov time with geometric Euclidean time.

### 7. Geometric one-layer OS Hilbert completion and identity obstruction

The actual finite Wilson one-layer reflection form has been completed into a geometric OS Hilbert space. The dense raw-observable embedding has exactly the original Wilson one-layer form as its inner product.

Consequently:

```text
a bounded operator reproduces every unshifted one-layer matrix element
  iff
that operator is the identity transfer.
```

Every nonidentity candidate has a concrete observable-pair matrix-element defect. Thus a nontrivial transfer cannot be obtained by renaming the unshifted reflection form.

### 8. Independent shifted geometric kernel and discrete semigroup

Given an independent shifted geometric kernel certificate with:

```text
exact raw-carrier realization
contraction
OS symmetry
nonnegative quadratic form
OS-null preservation,
```

the repository constructs:

```text
a separated-quotient endomorphism
a unique bounded operator on the completed OS Hilbert space
a symmetric positive contraction
natural-number iterates
the additive discrete semigroup law
exact represented-state action
exact iterated shifted-kernel matrix elements.
```

The shifted form is compared exactly with the unshifted reflection form. Equality for every observable pair forces the shifted operator to be the identity.

### 9. Exact comparison with beta-zero heat-bath dynamics

The geometric OS carrier and the beta-zero boundary heat-bath carrier are kept type-distinct and related only through an explicit linear isometry.

The integrated comparison defines exact defects for:

```text
shifted geometric matrix elements versus the unshifted Wilson form
shifted geometric evolution versus sampled beta-zero heat-bath evolution.
```

Zero bridge defect propagates to every natural-time power and every adjoint compression. Nonzero defect gives an exact no-go witness. No equality is inferred merely from similar semigroup notation.

### 10. Conditional finite-to-continuum mass-gap route

The repository contains theorem generators routing:

```text
tail-uniform finite Gibbs coercivity
boundary transfer contraction
finite reflected-integral decay
completed vacuum decay
strong/operator/form convergence inputs
```

to continuum right-Hamiltonian coercivity, graph-closed coercivity, and vacuum-kernel conclusions.

These downstream implications are formalized. The remaining task is to construct one concrete approximation family satisfying the required finite, geometric OS, convergence, and normalization hypotheses in a physically relevant four-dimensional regime.

## Current mathematical frontier

The immediate frontier is no longer the abstract construction of an OS Hilbert completion or a generic semigroup comparison calculus. Those layers are integrated.

The decisive open chain is:

```text
construct a concrete shifted Wilson kernel from genuine time-separated
finite-volume gauge-field geometry
  -> prove its contraction, positivity, and OS-null preservation
  -> identify or quantitatively control its exact comparison defect
     with the canonical boundary heat-bath evolution
  -> prove the actual OS boundary-moment intertwining
  -> obtain a nonzero-coupling geometric transfer estimate
  -> establish a tail-uniform finite-volume gap along a specified
     lattice-spacing / coupling / volume trajectory
  -> construct the continuum Euclidean Yang--Mills measure
  -> prove compatible operator or closed-form convergence
  -> identify the reconstructed physical Hamiltonian
  -> transfer the spectral lower bound
  -> fix physical-unit normalization and identify the physical mass scale.
```

A parallel finite-side obligation remains: replace or generate the scale-wise centered random-scan Rayleigh certificates directly from the explicit Wilson interaction in the required scaling regime, rather than leaving them as quantitative certificate data.

## Theorem boundary

| Surface | Status on the authoritative carrier |
|---|---|
| R4 OS quotient, completion, semigroup, generator, and Hamiltonian infrastructure | integrated |
| Reconstructed PVM support and bounded-Borel calculus | integrated |
| Exact lower-spectrum consequences from a supplied construction spine | integrated |
| Physical construction of that continuum spine | open |
| Finite periodic compact-Haar `SU(N)` Wilson Gibbs and heat-bath infrastructure | integrated |
| Explicit bounded-test Dobrushin matrix and small-coupling coefficient | integrated |
| `L²` Poincare from total variation alone | not claimed |
| `L²` Poincare/coercivity from explicit coefficient bounds plus genuine Rayleigh certificates | integrated |
| Canonical boundary Haar-to-Gibbs isometry and adjoint compression | integrated |
| General generator-leakage and semigroup-curvature calculus | integrated |
| Exact beta-zero boundary heat-bath semigroup and sharp gap one | integrated |
| Nonzero-beta analyzed-range invariance | open |
| Unshifted one-layer geometric OS Hilbert completion | integrated |
| Identity obstruction for the unshifted one-layer form | integrated |
| Shifted geometric OS operator and discrete semigroup from an independent certificate | integrated |
| Concrete shifted kernel derived from actual nonzero-coupling Wilson time translation | open |
| Exact geometric-OS / heat-bath identification | open; exact defect calculus integrated |
| Tail-uniform finite-volume gap from supplied scale-wise quantitative certificates | integrated |
| Tail-uniform gap derived in a specified physical continuum scaling regime | open |
| Continuum OS measure and interacting four-dimensional gauge model | open |
| Continuum Hamiltonian identification and spectral transfer | open |
| `exactGapValueReal = 33/20` as an internal normalized theorem route | integrated |
| `33/20` derived as a physical Yang--Mills mass scale | not claimed |
| Unconditional Clay Millennium existence and mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal` is the public projection of the current Hamiltonian/PVM/spectral theorem package. Its exact value `33/20` belongs to an internal normalized formal route.

The following obligations remain mathematically distinct:

```text
internal exact-spectrum normalization
finite-volume coercivity
tail-uniformity
geometric Euclidean-time transfer
continuum measure construction
operator or form convergence
continuum spectral transfer
physical-unit normalization
physical mass identification.
```

No internal normalization constant is treated as a measured or derived physical mass until all of those links are supplied by one concrete model.

## Replay

Pinned Lean toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Pinned mathlib revision:

```text
5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

From a fresh clone:

```bash
git checkout formal/real-hilbert-uniform-coercive-strong-limit
lake update
lake build
```

The repository also uses a focused **PR Lean Fast Check** for theorem-layer changes.

Before treating a result as integrated, verify:

```text
exact base SHA
fixed final head SHA
completed successful workflow, job, and required steps
squash integration
post-merge identity with the authoritative carrier.
```

## Development discipline

The active workflow is:

```text
start from the exact authoritative-carrier SHA
create one mathematically coherent branch
open a Draft pull request
keep theorem statements and physical assumptions unchanged
validate the fixed final head
mark ready only after completed successful evidence
squash merge with the expected head SHA fixed
verify post-merge identity
continue from the new carrier head.
```

The default `main` branch is the public landing surface. Current theorem authority is determined by `formal/real-hilbert-uniform-coercive-strong-limit`; public documentation should be synchronized from the validated carrier rather than inferred from stale open branches.
