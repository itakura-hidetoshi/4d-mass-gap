# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository contains substantial operator-theoretic infrastructure, explicit finite-volume Wilson systems, and a completed finite high-temperature `Z₂` geometric-transfer gap theorem. It does **not** currently construct interacting four-dimensional continuum Yang--Mills theory unconditionally, and it does **not** claim a proof of the Clay Millennium problem.

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

## Authoritative status — 2026-08-07 JST

```text
latest integrated theorem checkpoint:
  PR #1407
  Realize actual Z2 defect on finite probability L2

fixed PR head:
  b0b284a085694ca7c951229c91184c207b6105dd

authoritative carrier / squash integration:
  2b0ff76af45559ee81a9d47d8751db22a999ca70

validation:
  PR Lean Fast Check #9258
  run id 31127171274
  job id 92702662214
  completed / success

terminal build:
  Build completed successfully (8757 jobs)

artifact:
  lean-fast-check-log
  id 8974720827
  sha256:afcea206e56e63c28e27ff02f8609dfeaecd4b8f0dccb2aa4b69cc90c8359fa4

post-merge comparison:
  2b0ff76af45559ee81a9d47d8751db22a999ca70
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Only results merged into the authoritative carrier count as current theorem status. Open, Draft, stale, superseded, or closed-unmerged pull requests are not authoritative unless their content is subsequently integrated.

The current open Draft, PR #1409, attempts the next concrete residual-gauge-orbit probability `L²` realization. It is **not** counted below because its final head has no completed pull-request CI evidence yet.

## Executive summary

The development now has six connected lanes.

```text
A. continuum OS / Hamiltonian / PVM / exact-spectrum infrastructure

Euclidean and reflection-positive input
  -> OS quotient and real Hilbert completion
  -> semigroup, generator, and self-adjoint Hamiltonian interfaces
  -> bounded-Borel PVM calculus and spectral support
  -> exact lower-spectrum consequences from a supplied construction spine


B. finite compact-Haar SU(N) Gibbs and heat-bath analysis

compact Wilson Gibbs law
  -> exact one-link conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit Dobrushin influence matrices
  -> genuine L2 Rayleigh input
  -> finite Gibbs Poincare/coercivity and centered decay


C. actual finite even-four-torus Z2 geometric transfer

adjacent-slice Wilson slab kernel
  -> residual Gauss projection and temporal-link summation
  -> symmetric positive normalized one-slab transfer
  -> Perron ground state and complete finite spectral decomposition
  -> correct-marginal posterior coupling and coordinate response
  -> direct full-transfer spectral cap 1/2
  -> volume-independent geometric Dirichlet coercivity 1/2


D. varying-Hilbert strong-limit preservation

finite ground-lifted defects with common coercivity 1/2
  -> supplied approximation maps and isometric embeddings
  -> supplied approximation and evolved convergence
  -> limiting coercivity 1/2
  -> limiting real spectrum in [1/2, infinity)
  -> zero resolvent and inverse norm at most 2


E. projective-limit L2 common-carrier machinery

finite-marginal L2 pullback isometries
  -> directed finite-coordinate cylinder subspaces
  -> topological density of their algebraic supremum
  -> compatible finite operators on cylinder ranges
  -> unique bounded continuum L2 operator extension
  -> conditional actual-Z2-to-marginal operator transport


F. concrete finite probability realizations

finite-dimensional real Hilbert carrier
  -> strict finite-probability L2 coordinates
  -> orthonormal diagonal multiplication realization
  -> actual Z2 spectral-probability carrier
  -> exact pointwise ground-lifted defect
  -> exact coercivity 1/2 on the whole finite probability carrier
```

The decisive advance since the previous documentation is that the full finite high-temperature `Z₂` geometric one-slab gap is no longer open. The integrated chain now derives a direct coordinate-response matrix, transports it to the exact geometric Perron--Doob row, proves a common excited-transfer cap `1/2`, and closes the full spatially sandwiched transfer package. The main unresolved problem has moved from **finite-volume gap construction** to **constructing the actual cross-volume probability/marginal system and its continuum convergence**.

## What is formally integrated

### 1. Continuum-facing OS, Hamiltonian, and exact-spectrum infrastructure

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

the repository derives the exact lower-spectrum package associated with `exactGapValueReal`, including:

```text
vacuum energy at zero
absence of spectrum in the open interval below the threshold
threshold membership
least nonzero spectral value
infimum characterization of the nonzero spectrum
first-excitation identification
uniqueness of the least nonzero spectral energy.
```

The integrated infrastructure also includes:

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
strongly continuous semigroup routes
generator-domain and graph-closure machinery
self-adjoint Hamiltonian interfaces
simple-function and bounded-Borel PVM integration
quadratic scalar spectral measures
polarization, multiplicativity, and support identification.
```

These are theorem consequences from supplied construction data. They do not construct the interacting continuum gauge model required by the Clay problem.

### 2. Finite compact-Haar `SU(N)` Wilson Gibbs and heat-bath layer

The compact finite-volume lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure. It constructs:

```text
finite periodic Wilson Gibbs probability
exact one-link conditional probabilities
one-link heat-bath projections
Gibbs reversibility and Hilbert projection structure
conditional-variance and Dirichlet identities
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

Total-variation or bounded-test contraction is not silently promoted to an `L²` spectral gap. The compact-Haar `L²` Poincare and coercivity packages retain genuine centered Rayleigh data where required.

### 3. Canonical boundary analysis and exact beta-zero closure

The canonical finite boundary analysis is built from measure geometry:

```text
boundary projection pullback
  -> full product-Haar L2
  -> multiplication by sqrt(Z) * exp(-S/2)
  -> finite Wilson Gibbs L2.
```

Its real-Hilbert adjoint gives canonical synthesis. The repository constructs compressed Hamiltonians and semigroups, vacuum transport, generator leakage, second-moment curvature, and zero-defect intertwining theorems.

At `beta = 0`, the actual periodic-even compact Wilson system has exact product-Haar normalization, zero leakage and curvature, sharp boundary coercivity one, zero-mode exclusion, and exact all-real-time compressed heat-bath evolution. This remains a finite beta-zero heat-bath theorem, not an interacting continuum or geometric-time identification.

### 4. Actual finite `Z₂` adjacent-slice geometric transfer

The finite even-four-torus `Z₂` lane constructs genuine adjacent-slice Euclidean lattice time:

```text
spatial boundary configurations
  -> crossing plaquette kernel
  -> spatial half-action sandwich
  -> exact one-slab Boltzmann kernel
  -> temporal-link summation
  -> residual Gauss projection
  -> Gauss-invariant Hilbert transfer
  -> operator-norm normalization.
```

The result is a symmetric positive norm-one contraction with natural-time powers. The carrier also proves:

```text
finite-order periodic-permutation no-go
nonidentity of the actual slab transfer
complete finite spectral decomposition
positive Perron ground ray and its simplicity
injectivity at strict coupling
absence of a finite-volume null sector
positive excitation gap at every finite volume.
```

This is geometric one-slab time. It is not random-scan or heat-bath Markov time.

### 5. Actual high-temperature posterior and correct-marginal coupling

Starting from the exact zero-coupling seed, the repository constructs continuity of the actual Perron ground and posterior influence data. It selects a positive, volume-independent high-temperature cutoff and obtains strict row-and-column Dobrushin data at every finite side and boundary environment.

The subsequent coupling package supplies:

```text
single-site overlap couplings with exact marginals
parallel product couplings with exact kernel marginals
Hamming disagreement and spatial-sandwich stability
stationary uniqueness and random-scan mixing
total-variation and finite-dimensional strong convergence
observable-response transport
residual-gauge and unfixed-gauge mixture transport.
```

The residual-gauge latent index law is proved uniform and environment-independent, so the latent mismatch term vanishes exactly. The remaining same-index posterior response is then primalized from Hamming-dual control to coordinatewise overlap-coupling mismatch.

### 6. Direct full geometric `Z₂` uniform gap

The coordinate response is linearized into a nonnegative finite matrix. On a positive volume-independent direct-response cutoff interval, every source column has strict sum below `1/2`.

That matrix is transported to the exact geometric Perron--Doob observable row. The integrated theorem chain proves, for every finite side in the common interval:

```text
weighted mean-zero Doob quadratic <= (1/2) * weighted norm squared

every strictly excited normalized transfer eigenvalue <= 1/2

(1/2) * weighted norm squared
  <= geometric Doob Dirichlet form
```

Exact Perron conjugacy then closes the full spatially sandwiched one-slab package, including:

```text
volume-independent centered Rayleigh contraction
volume-independent Poincare / Dirichlet coercivity 1/2
uniform excited-transfer spectral cap 1/2
positive excitation-energy floor
natural-time centered decay.
```

This is the actual finite high-temperature `Z₂` full geometric transfer gap theorem. Random scan appears only as a stationary comparison tool inside the proof and is not identified with geometric time.

### 7. Ground-lifted defect and conditional strong-limit preservation

For a finite symmetric positive contraction, the repository defines a ground-lifted defect that is the identity on the ground sector and agrees modewise with `I - T` on excited and null modes.

For the actual finite `Z₂` transfer, the common spectral cap gives the basis-free bound

```text
(1/2) * ||f||^2 <= inner(D_H f, f)
```

on the whole finite ground-lifted carrier.

Given explicitly supplied varying-Hilbert approximation data—approximation maps, isometric embeddings, a common limit operator, approximation convergence, and evolved convergence—the strong-limit package preserves the exact constant:

```text
(1/2) * ||f||^2 <= inner(D_infinity f, f)

spectrum ℝ D_infinity ⊆ [1/2, infinity)

0 ∈ resolventSet ℝ D_infinity

||D_infinity^{-1}|| <= 2.
```

The convergence data are inputs. The repository proves preservation under such a limit; it does not yet construct the physical thermodynamic or continuum limit.

### 8. Projective-limit `L²` cylinder system and density

For an existing projective-limit probability measure, the repository constructs canonical real-linear isometric pullbacks

```text
tau[J,I] : L2(Q J) -> L2(Q I)
iota[J]   : L2(Q J) -> L2(mu)
```

for finite coordinate sets `J ⊆ I`, with exact compatibility

```text
iota[J](f) = iota[I](tau[J,I](f)).
```

Their ranges form a directed family of finite-coordinate cylinder subspaces. The algebraic supremum is not asserted to equal the whole carrier; instead the repository proves the correct topological statement:

```text
topologicalClosure (sup_J cylinderSubspace(J)) = top.
```

No countable skeleton or standard-Borel assumption is inserted into this density theorem beyond the stated finite-measure projective-limit setting.

### 9. Compatible finite-marginal operators extend uniquely to continuum `L²`

A uniformly bounded family of finite-marginal `L²` operators with exact transition intertwining is conjugated to the continuum cylinder ranges. Compatibility on arbitrary overlaps is proved by transporting both finite coordinate sets into their union.

The operators are then:

```text
glued on the algebraic total cylinder core
  -> shown uniformly bounded there
  -> extended by cylinder density
  -> bundled as one bounded continuum L2 operator.
```

The extension satisfies exact finite-to-continuum intertwining, the common pointwise and operator-norm bounds, and uniqueness among bounded continuum operators with those finite-marginal restrictions.

This is an operator-extension theorem from a compatible finite family. It does not itself construct the actual physical family or prove evolved strong convergence.

### 10. Conditional actual-`Z₂` to projective-marginal bridge

The actual finite `Z₂` transfer carrier is a Gauss-invariant finite Hilbert subspace, whereas an arbitrary Euclidean projective marginal is a full measure-theoretic `L²` space. The repository therefore does not assert a false unconditional equality between them.

Instead it isolates explicit model-facing data:

```text
selected finite Euclidean coordinate sets
mutually inverse real-linear isometries
actual ground-lifted defect realization on each selected marginal
one compatible finite-marginal operator system.
```

From these inputs it proves exact operator intertwining, symmetry, exact coercivity `1/2`, continuum cylinder embedding, equality of embedded quadratic forms, and coercivity `1/2` on every embedded actual finite carrier.

The explicit identification and compatible system remain to be constructed from the concrete gauge geometry.

### 11. Concrete finite spectral-probability `L²` realization

Every finite-dimensional real Hilbert space is identified, through an orthonormal basis, with a strict finite-probability `L²` carrier using square-root-density coordinates. Diagonal operators become literal pointwise multiplication.

For the actual finite Gauss-invariant `Z₂` transfer carrier, the repository uses the canonical finite eigenbasis and uniform probability on the spectral index set. It proves:

```text
exact mutually inverse linear isometries
actual ground-lifted defect = pointwise lifted-defect multiplication
exact operator conjugacy and intertwining
exact diagonal quadratic-form identity
symmetry
coercivity 1/2 on the whole probability carrier.
```

This is a concrete finite spectral-probability realization. The spectral index probability is not claimed to be the Euclidean projective marginal or the residual gauge-orbit probability.

## Current mathematical frontier

The finite full-transfer gap itself is closed. The immediate frontier is now the concrete carrier and limit construction:

```text
construct the actual residual-gauge orbit probability space
  -> identify the Gauss-invariant finite carrier with orbit-probability L2
  -> realize the ground-lifted defect on that concrete orbit carrier
  -> build cross-volume orbit/marginal transition maps
  -> embed the actual finite carriers into one compatible projective family
  -> construct the compatible finite-marginal operator system
  -> prove approximation and evolved strong convergence
  -> construct a thermodynamic / continuum limit carrying coercivity 1/2.
```

The active Draft PR #1409 addresses the first three arrows, but it is not authoritative until completed final-head CI and the normal merge audit exist.

The larger physical program then remains:

```text
replace or extend the finite Z2 mechanism to compact SU(2) / SU(N)
  -> choose a physically relevant lattice-spacing, coupling, and volume trajectory
  -> prove tail-uniform geometric and regularity estimates
  -> construct a nontrivial continuum Euclidean Yang--Mills measure
  -> prove reflection positivity, covariance, clustering, and regularity
  -> identify the OS-reconstructed physical Hamiltonian
  -> transfer a strict spectral lower bound
  -> fix physical units and identify the physical mass scale.
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
| Compact `SU(N)` `L²` coercivity from total variation alone | not claimed |
| Canonical boundary isometry, compression, leakage calculus, and beta-zero closure | integrated |
| Actual finite even-four-torus `Z₂` adjacent-slice transfer | integrated |
| Perron ground simplicity and complete finite spectral decomposition | integrated |
| Actual high-temperature posterior interval and correct-marginal coupling | integrated |
| Direct coordinate-response matrix with strict source columns below `1/2` | integrated |
| Full spatially sandwiched geometric `Z₂` transfer cap `1/2` | integrated |
| Full geometric `Z₂` Dirichlet/coercivity constant `1/2` | integrated |
| Ground-lifted strong-limit preservation of `1/2` from supplied convergence data | integrated |
| Construction of the physical strong/thermodynamic/continuum limit | open |
| Projective-limit finite-marginal `L²` isometric system | integrated |
| Density of finite-coordinate cylinder subspaces | integrated |
| Unique bounded extension of compatible finite-marginal operators | integrated |
| Explicit actual-`Z₂` finite carrier identification with selected Euclidean marginals | model-facing input; open |
| Concrete spectral-probability `L²` realization of the finite carrier | integrated |
| Concrete residual gauge-orbit probability `L²` realization | active Draft; not integrated |
| Cross-volume gauge-orbit/marginal transition system | open |
| Compact `SU(2)` / `SU(N)` analogue of the geometric full-gap theorem | open |
| Continuum Euclidean Yang--Mills measure and OS/Wightman closure | open |
| `exactGapValueReal = 33/20` as an internal normalized theorem route | integrated |
| `33/20` as a derived physical Yang--Mills mass | not claimed |
| Unconditional Clay Millennium theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal = 33/20` belongs to an internal normalized theorem route. It is mathematically distinct from:

```text
the finite Z2 transfer cap 1/2
the finite ground-lifted defect coercivity 1/2
a continuum coercivity constant transported from supplied convergence data
a physical mass in fixed units.
```

No equality among these quantities is inferred without an explicit theorem connecting the corresponding carriers, limits, Hamiltonians, and unit normalizations.

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
completed workflow, job, required steps, and artifact evidence
squash integration with expected_head_sha fixed
post-merge identity with the authoritative carrier.
```

## Development discipline

The active workflow is:

```text
start from the exact authoritative-carrier SHA
create one mathematically coherent branch
open a Draft pull request
keep theorem statements and physical assumptions unchanged
write no branch commits while CI is queued or in progress
separate code failures from GitHub Actions or external infrastructure failures
validate the fixed final head
mark Ready only after completed successful evidence
squash merge with expected_head_sha fixed
verify post-merge identity
continue from the new carrier head.
```

The default `main` branch is the public landing surface. Current theorem authority is determined by `formal/real-hilbert-uniform-coercive-strong-limit`; after validated documentation is integrated there, the exact README and ROADMAP blobs should be synchronized to `main`.
