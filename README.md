# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository contains substantial theorem infrastructure and several concrete finite-volume Wilson constructions. It does **not** currently contain an unconditional construction of interacting four-dimensional continuum Yang--Mills theory, and it does **not** claim a proof of the Clay Millennium problem.

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md

KuuOS reference bridge:
  docs/kuuos_reference_bridge.md
```

## Authoritative status — 2026-08-06 JST

```text
latest integrated theorem checkpoint:
  PR #1391
  Construct correct-marginal parallel Doob coupling
  and spatial sandwich contraction

fixed PR head:
  a276308b86d060f6f406de0f45e2afe51fb68192

authoritative carrier / squash integration:
  eaade95477ee0cf354d265b14d08123aec1ff52f

validation:
  PR Lean Fast Check #9184
  run id 31078935258
  job id 92543058944
  completed / success

terminal build:
  Build completed successfully (8686 jobs)

post-merge comparison:
  eaade95477ee0cf354d265b14d08123aec1ff52f
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Only results merged into the authoritative carrier count as current theorem status. Open, Draft, stale, superseded, or closed-unmerged pull requests are historical or experimental unless their content has subsequently been integrated.

## Executive summary

The formal development now has five distinct but connected lanes.

```text
A. continuum OS / Hamiltonian / PVM / exact-spectrum infrastructure

Euclidean and reflection-positive input
  -> OS quotient and real Hilbert completion
  -> semigroup, generator, and self-adjoint Hamiltonian interfaces
  -> bounded-Borel PVM calculus and spectral support
  -> exact lower-spectrum consequences from a supplied construction spine


B. finite periodic compact-Haar SU(N) Gibbs and heat-bath analysis

compact Wilson Gibbs law
  -> exact one-link conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit Dobrushin influence matrix
  -> genuine L2 Rayleigh input
  -> finite Gibbs Poincare/coercivity and centered decay


C. canonical boundary analysis and comparison

boundary Haar L2
  -> canonical Haar-to-Gibbs analysis isometry
  -> Hilbert-adjoint synthesis
  -> compressed Hamiltonian and semigroups
  -> leakage and curvature defects
  -> exact beta-zero boundary closure
  -> explicit comparison defects between distinct dynamics


D. actual finite even-four-torus Z2 geometric one-slab transfer

periodic time-translation permutation no-go
  -> adjacent-slice Wilson slab kernel
  -> temporal-link sum and residual Gauss projection
  -> symmetric positive norm-one transfer
  -> full finite spectral decomposition
  -> Perron ground-state simplicity
  -> positive excitation gap at every finite volume
  -> crossing-only volume-independent gap


E. high-temperature Perron posterior and correct-marginal coupling

actual Perron-ground continuity at zero coupling
  -> actual posterior influence continuity
  -> volume-independent positive coupling cutoff
  -> strict row/column Dobrushin data at every finite volume
  -> correct-marginal parallel overlap coupling
  -> Hamming contraction and spatial-sandwich stability
  -> random-scan uniqueness, mixing, total-variation control,
     strong convergence, and observable-response transport
```

The decisive change since the previous documentation is that geometric time is no longer represented only by an abstract shifted-kernel certificate. The carrier now includes an actual finite `Z₂` adjacent-slice Wilson transfer, its gauge projection and temporal-link averaging, its finite spectral theory, and a concrete high-temperature posterior-coupling mechanism. The remaining finite-side problem is to turn the new coupling and spatial-sandwich control into a volume-uniform spectral estimate for the **full geometric one-slab transfer**, without identifying that transfer with random-scan or heat-bath Markov time.

## What is formally integrated

### 1. Exact-spectrum consequences from a supplied continuum construction spine

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

These are consequences of the fields of the supplied spine. They do not construct the required interacting continuum gauge model.

### 2. Reconstructed real Hilbert space, Hamiltonian, and PVM calculus

The integrated continuum-facing infrastructure includes:

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
physical semigroup and strong-continuity routes
generator-domain and graph-closure infrastructure
self-adjoint Hamiltonian interfaces
simple-function PVM integration
bounded-Borel operator-norm completion
quadratic scalar spectral measures
polarization and multiplicativity
spectral-support identification.
```

The lower threshold is characterized through support, leastness, and infimum statements. An isolated eigenvalue or positive singleton spectral atom requires additional model input unless separately proved.

### 3. Finite compact-Haar `SU(N)` Wilson Gibbs and heat-bath layer

The compact finite-volume lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure. It contains:

```text
finite periodic Wilson Gibbs probability
exact one-link conditional probabilities
one-link heat-bath projections
Gibbs reversibility and Hilbert projection structure
native conditional-variance and Dirichlet identities
shared-plaquette localization
explicit bounded-test influence coefficients
volume-independent Dobrushin matrices.
```

The explicit coefficient package remains

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta
```

with strict bounded-test contraction in

```text
beta < log (19 / 17) / 4.
```

This total-variation / bounded-test estimate is not promoted to an `L²` spectral gap by itself. The integrated `L²` Poincare and coercivity packages retain genuine centered Rayleigh data where required.

### 4. Canonical boundary analysis, compression, and beta-zero closure

The boundary map is constructed from measure geometry:

```text
boundary projection pullback
  -> full product-Haar L2
  -> multiplication by sqrt(Z) * exp(-S/2)
  -> finite Wilson Gibbs L2.
```

Its real-Hilbert adjoint gives canonical synthesis. The carrier constructs:

```text
compressed boundary Hamiltonian A* H_HB A
full and centered compressed heat-bath evolutions
vacuum transport and centering compatibility
generator leakage D = H_HB A - A H_boundary
second-moment curvature Q = A* H_HB^2 A - H_boundary^2
exact zero-defect all-time semigroup and intertwining theorems.
```

At `beta = 0`, the actual periodic-even compact Wilson system has exact product-Haar normalization, zero leakage and curvature, sharp boundary coercivity constant one, zero-mode exclusion, and an exact all-real-time compressed semigroup. This remains a finite beta-zero heat-bath result, not a geometric-time or interacting-continuum theorem.

### 5. Geometric one-layer obstruction and periodic-permutation no-go

The unshifted Wilson reflection form completes to the inner product of its geometric OS Hilbert space. Therefore any bounded operator reproducing every unshifted matrix element is the identity.

The actual one-step translation on the finite periodic even four-torus has finite order. The carrier proves that a finite-order operator which is simultaneously contractive, symmetric, and positive in quadratic form must be the identity. Thus a nontrivial geometric Wilson transfer cannot be obtained by treating periodic time translation as an invertible permutation of the positive-configuration carrier.

The required replacement is an adjacent-layer transfer kernel obtained after summing or integrating slab-interior variables.

### 6. Actual finite `Z₂` adjacent-slice Wilson transfer

The repository constructs the actual finite even-four-torus `Z₂` one-slab transfer through:

```text
spatial time-slice configurations
  -> temporal-gauge crossing plaquette kernel
  -> spatial half-action sandwich
  -> exact one-slab Boltzmann kernel
  -> finite Euclidean boundary Hilbert operator
  -> operator-norm normalization
  -> symmetric positive norm-one contraction
  -> natural-time powers.
```

It then adds:

```text
residual slice-gauge action and Gauss projection
temporal-link field and exact temporal-link summation
unfixed-gauge one-slab kernel
separate gauge invariance on both boundaries
compression to the Gauss-invariant Hilbert carrier
explicit nonidentity witnesses.
```

This is genuine adjacent-slice geometric lattice time. It is not random-scan or heat-bath time.

### 7. Finite `Z₂` spectral and Perron packages

For the normalized Gauss-invariant unfixed-gauge transfer, the carrier constructs:

```text
canonical finite-dimensional eigenbasis
positive spectral-support transfer
support Hamiltonian E = -log(lambda) for lambda > 0
full ground / excited / null decomposition
natural-time mode evolution
extended energy with separate infinite null energy
kernel, fixed-space, and range characterizations.
```

For strict coupling

```text
0 < beta
energyIdentity < energyNontrivial,
```

the local crossing matrix is positive definite. Tensor positivity and positive diagonal sandwiching imply injectivity of the full finite transfer. Consequently:

```text
null sector is absent at every finite volume
Perron ground ray is unique and pointwise positive
strictly excited sector is nonempty at every finite volume
each finite volume has a strictly positive excitation gap
excited coordinates have exact exponential natural-time decay.
```

The gap here may depend on the finite side parameter. Positivity at every finite volume is not the same as a uniform lower bound.

### 8. Uniform-gap interfaces and crossing-only theorem

The generic finite-dimensional layer proves exact equivalences among:

```text
a common excited-transfer spectral cap rate < 1
a uniform centered Rayleigh contraction
a uniform centered Poincare coercivity
a positive volume-independent excitation-energy floor.
```

For the actual temporal-crossing tensor-product backbone of the finite `Z₂` model, the repository proves a genuine volume-independent estimate. With

```text
w0 = exp(-beta * energyIdentity)
w1 = exp(-beta * energyNontrivial)
q  = (w0 - w1) / (w0 + w1)
kappa = 1 - q
Delta_cross = -log(q),
```

strict coupling gives `0 < q < 1`, `0 < kappa`, and a dimension-independent centered contraction and Poincare bound, including after Gauss compression.

This theorem applies to the normalized **crossing-only** transfer. The spatial half-action sandwich requires an additional stability argument before the same conclusion can be asserted for the full one-slab transfer.

### 9. Spatial sandwich and actual high-temperature Perron posterior

The full one-slab kernel is factored exactly as

```text
T_full = M_a * T_cross * M_a
```

with the actual spatial half-Boltzmann multiplier `M_a`. The global extremal ratio grows with the number of spatial plaquettes, proving that a crude whole-volume comparison cannot yield a uniform estimate.

The subsequent high-temperature development instead constructs a local hidden-posterior route:

```text
exact local shared-plaquette influence
  -> canonical finite posterior envelope kernels
  -> bidirectional row/column recurrences
  -> persistent barrier propagation
  -> continuous first-exit closure
  -> continuity of the actual normalized Perron ground
  -> exact zero-coupling posterior seed
  -> positive volume-independent coupling cutoff.
```

For every

```text
0 < beta <= couplingCutoff,
```

every finite side and every boundary environment receives actual strict row-and-column Dobrushin data for the Perron-smoothed posterior. The fixed continuation barrier is `1/2`; the cutoff is selected from exact zero-coupling continuity rather than assumed.

### 10. Correct-marginal parallel coupling, stability, and mixing

The latest integrated package constructs:

```text
single-site overlap couplings with exact marginals
coordinatewise product couplings for parallel conditional resampling
exact left and right parallel-kernel marginals
expected Hamming-disagreement estimates
bidirectional strict Dobrushin contraction
actual specialization throughout the high-temperature interval.
```

For arbitrary hidden slices, expected coordinate disagreement is bounded by

```text
(1/2 * barrier) * HammingDistance,
```

and `1/2 * barrier < 1`. If two inputs agree outside a finite interior set, the spatial-sandwich disagreement is bounded by

```text
(1/2 * barrier) * interior.card.
```

The same package derives random-scan coupling iteration, stationary uniqueness, mixing, total-variation control, finite-dimensional strong convergence, observable-response bounds, residual-gauge isometry, and unfixed-gauge mixture transport.

These are actual finite high-temperature posterior and Markov-chain theorems. They do not by themselves identify the random-scan gap with the geometric full one-slab transfer gap.

## Current mathematical frontier

The immediate finite-side frontier is now sharply localized:

```text
actual high-temperature posterior Dobrushin data
  + correct-marginal parallel coupling
  + spatial-sandwich Hamming stability
  + crossing-only uniform geometric gap

  -> derive a centered Rayleigh / Poincare / spectral-cap estimate
     for the actual full spatially sandwiched geometric one-slab transfer
  -> prove one positive volume-independent full-transfer gap
     throughout an explicit high-temperature interval
  -> keep that geometric transfer distinct from random-scan and heat-bath time.
```

After that finite `Z₂` theorem, the larger model chain remains:

```text
extend or replace the finite Z2 mechanism on compact SU(2) / SU(N)
  -> specify a physically relevant lattice-spacing, coupling, and volume trajectory
  -> prove tail-uniform geometric transfer and regularity estimates
  -> construct a nontrivial continuum Euclidean Yang--Mills measure
  -> prove reflection positivity, covariance, clustering, and regularity
  -> establish operator or closed-form convergence
  -> identify the reconstructed physical Hamiltonian
  -> transfer a strict spectral lower bound
  -> prove physical-unit normalization and identify the physical mass scale.
```

## Theorem boundary

| Surface | Status on the authoritative carrier |
|---|---|
| OS quotient, real Hilbert completion, semigroup, generator, and Hamiltonian infrastructure | integrated |
| PVM support and bounded-Borel calculus | integrated |
| Exact lower-spectrum consequences from a supplied continuum spine | integrated |
| Construction of that interacting continuum spine | open |
| Finite periodic compact-Haar `SU(N)` Gibbs and heat-bath infrastructure | integrated |
| Compact `SU(N)` bounded-test Dobrushin coefficient | integrated |
| Compact `SU(N)` `L²` coercivity from TV alone | not claimed |
| Compact `SU(N)` `L²` coercivity from explicit coefficient plus genuine Rayleigh data | integrated |
| Canonical boundary isometry, adjoint compression, and leakage calculus | integrated |
| Exact beta-zero compact boundary semigroup | integrated |
| Geometric one-layer Hilbert completion and identity obstruction | integrated |
| Finite-order periodic-permutation no-go | integrated |
| Actual finite even-four-torus `Z₂` one-slab Wilson transfer | integrated |
| Residual Gauss projection and unfixed temporal-link sum | integrated |
| Full finite spectral decomposition and Perron ground simplicity | integrated |
| Positive excitation gap separately at every strict-coupling finite volume | integrated |
| Volume-uniform gap for the crossing-only `Z₂` backbone | integrated |
| Volume-uniform gap for the full spatially sandwiched `Z₂` transfer | open |
| Actual high-temperature Perron posterior Dobrushin interval | integrated |
| Correct-marginal parallel posterior coupling and spatial-sandwich stability | integrated |
| Random-scan uniqueness, mixing, TV control, and strong convergence | integrated |
| Identification of random-scan/heat-bath time with geometric one-slab time | not claimed |
| Compact `SU(2)` / `SU(N)` analogue of the actual one-slab spectral package | open |
| Tail-uniform gap along a physical continuum scaling trajectory | open |
| Continuum Euclidean Yang--Mills measure | open |
| Continuum Hamiltonian identification and spectral transfer | open |
| `exactGapValueReal = 33/20` as an internal normalized theorem route | integrated |
| `33/20` as a derived physical Yang--Mills mass | not claimed |
| Unconditional Clay Millennium theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal = 33/20` belongs to an internal normalized theorem route. The following remain distinct obligations:

```text
internal exact-spectrum normalization
finite-volume geometric transfer gap
volume-uniformity
compact-gauge extension
physical continuum scaling
continuum measure construction
operator or form convergence
continuum spectral transfer
physical-unit normalization
physical mass identification.
```

No internal normalization constant is treated as a measured or derived physical mass before one concrete model discharges the complete chain.

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

The focused **PR Lean Fast Check** is used for theorem-layer changes. Before treating a result as integrated, verify the exact base, fixed final head, completed successful workflow/job/steps, squash integration, and post-merge identity with the authoritative carrier.

## Development discipline

The active workflow is:

```text
start from the exact authoritative-carrier SHA
create one mathematically coherent branch
open a Draft pull request
keep theorem statements and physical assumptions unchanged
validate the fixed final head
mark ready only after completed successful evidence
squash merge with expected_head_sha fixed
verify post-merge identity
synchronize README and ROADMAP to public main
continue from the new authoritative head.
```

The default `main` branch is the public landing surface. Mathematical authority remains the validated `formal/real-hilbert-uniform-coercive-strong-limit` carrier; public documentation must be synchronized from that carrier after integration.
