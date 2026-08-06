# MGAP4D Roadmap

This document records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

It separates:

- theorem infrastructure already replayed on the authoritative carrier;
- concrete finite compact-gauge and finite `Z₂` Wilson results;
- the completed finite high-temperature geometric-transfer gap;
- projective-limit and varying-Hilbert operator machinery;
- model-facing carrier and convergence obligations; and
- claims that are explicitly not made.

## Snapshot — 2026-08-07 JST

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #1407
  Realize actual Z2 defect on finite probability L2

fixed integrated PR head:
  b0b284a085694ca7c951229c91184c207b6105dd

latest authoritative carrier / squash integration:
  2b0ff76af45559ee81a9d47d8751db22a999ca70

latest completed validation:
  PR Lean Fast Check #9258
  run id 31127171274
  job id 92702662214
  completed / success

terminal build:
  Build completed successfully (8757 jobs)

post-merge comparison:
  2b0ff76af45559ee81a9d47d8751db22a999ca70
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Open, Draft, stale, superseded, and closed-unmerged pull requests are not part of the authoritative theorem state.

Current active Draft:

```text
PR #1409
  Realize finite Z2 carrier on gauge-orbit probability L2

base:
  2b0ff76af45559ee81a9d47d8751db22a999ca70

candidate head:
  997bf6e19b8c5aeaa75e8c114955eea0d696eacc

status at this snapshot:
  Draft / mergeable
  no completed final-head pull-request CI evidence
  not authoritative
```

## Proof architecture

The repository now has six connected lanes.

```text
A. continuum reconstruction and exact-spectrum infrastructure

Euclidean / OS input
  -> reflection-positive quotient
  -> real Hilbert completion
  -> semigroup and generator
  -> self-adjoint Hamiltonian interfaces
  -> PVM and bounded-Borel calculus
  -> exact lower-spectrum consequences from a supplied spine
  -> concrete interacting continuum construction [open]


B. finite compact-Haar SU(N) analysis

Wilson Gibbs law
  -> exact conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit bounded-test Dobrushin matrices
  -> genuine L2 Rayleigh data where required
  -> finite Gibbs Poincare/coercivity and centered decay


C. actual finite even-four-torus Z2 geometric transfer

adjacent-slice slab kernel
  -> residual Gauss projection and temporal-link sum
  -> normalized symmetric positive transfer
  -> Perron ground and finite spectral decomposition
  -> high-temperature posterior coupling
  -> coordinate-response matrix
  -> excited-transfer cap 1/2
  -> full geometric Dirichlet coercivity 1/2


D. ground-lifted strong-limit preservation

finite full-carrier defect coercivity 1/2
  -> supplied varying-Hilbert approximation data
  -> limiting coercivity 1/2
  -> real spectrum in [1/2, infinity)
  -> zero resolvent
  -> inverse norm at most 2


E. projective-limit L2 operator system

finite-marginal pullback isometries
  -> directed cylinder subspaces
  -> topological cylinder density
  -> compatible finite operators
  -> algebraic-core gluing
  -> unique bounded continuum L2 extension
  -> selected actual-Z2 finite-carrier bridge


F. concrete probability carriers

finite Hilbert space
  -> strict finite-probability L2 coordinates
  -> spectral-probability realization
  -> pointwise ground-lifted defect
  -> residual gauge-orbit probability realization [active]
  -> cross-volume compatible probability/marginal system [open]
```

## Milestone ledger

### Milestone 0 — Authority, replay, and claim discipline

**Status: integrated and permanent.**

Required discipline:

```text
exact authoritative base
Draft start
fixed final head
completed workflow/job/step/artifact evidence
no branch writes while CI is queued or in progress
code failures separated from external Actions failures
Ready re-audit
squash merge with expected_head_sha fixed
post-merge identical comparison.
```

Only the authoritative carrier determines theorem status. The public `main` branch is a landing surface and must receive exact validated documentation blobs separately.

### Milestone 1 — Continuum OS, Hamiltonian, PVM, and exact-spectrum theorem infrastructure

**Status: integrated as theorem infrastructure.**

Integrated surfaces include:

```text
reflection-positive quotient and Hilbert completion
strong semigroup and generator routes
closed-graph and self-adjoint Hamiltonian interfaces
bounded-Borel PVM calculus
scalar spectral measures and support
exact-gap interval, leastness, infimum, and first-excitation consequences.
```

Boundary:

```text
the construction spine remains supplied input
the interacting continuum gauge measure is not constructed here
exactGapValueReal = 33/20 is an internal normalization route.
```

### Milestone 2 — Finite compact-Haar `SU(N)` Gibbs and heat-bath analysis

**Status: integrated.**

Integrated surfaces include:

```text
normalized compact Haar Wilson Gibbs probability
exact one-link conditionals
heat-bath projections and reversibility
conditional-variance / Dirichlet identities
shared-plaquette localization
explicit bounded-test Dobrushin coefficient
finite and tail-uniform L2 theorem generators with genuine Rayleigh input
canonical boundary analysis and beta-zero closure.
```

Permanent distinction:

```text
total variation or bounded-test control
  !=
L2 spectral gap without a genuine L2 argument.
```

### Milestone 3 — Actual finite `Z₂` geometric one-slab transfer

**Status: integrated.**

The carrier constructs:

```text
actual adjacent-slice Wilson slab kernel
spatial half-action sandwich
temporal-link summation
residual slice-gauge action and Gauss projection
normalized Gauss-invariant transfer
natural-time powers
complete finite spectral decomposition
positive simple Perron ground
injectivity and no finite null sector at strict coupling
positive excitation gap at each finite volume.
```

The finite-order periodic-permutation no-go is also integrated: an invertible periodic shift cannot be renamed into a nontrivial positive contractive transfer.

### Milestone 4 — High-temperature Perron posterior and exact-marginal coupling

**Status: integrated.**

The integrated route is:

```text
continuity of finite inverse matrices and Perron data
  -> exact zero-coupling posterior seed
  -> positive volume-independent continuation cutoff
  -> strict row/column posterior Dobrushin data
  -> exact-marginal parallel overlap coupling
  -> Hamming contraction and spatial-sandwich stability
  -> stationary uniqueness, mixing, TV, and strong convergence
  -> observable-response transport.
```

Residual-gauge latent index laws are uniform and environment-independent, so the latent mismatch contribution vanishes exactly.

### Milestone 5 — Coordinate-response matrix and full geometric gap

**Status: integrated.**

The previously open finite-side obstruction is closed.

Integrated chain:

```text
Hamming-dual response
  -> finite-probability total-variation primalization
  -> coordinate mismatch of the exact overlap coupling
  -> exact full-mixture response without latent error
  -> finite coordinate-response matrix
  -> strict source-column sums below 1/2
  -> actual geometric Doob variation certificate
  -> weighted mean-zero Rayleigh rate 1/2
  -> excited-transfer eigenvalue cap 1/2
  -> geometric Dirichlet coercivity 1/2
  -> full spatially sandwiched transfer package.
```

Authoritative finite theorem:

```text
for every finite side in one common positive high-temperature interval,
all strictly excited normalized geometric-transfer eigenvalues are <= 1/2,
and the exact geometric Doob Dirichlet form is coercive with constant 1/2.
```

Random scan is a stationary comparison device in the proof. It is not geometric one-slab time.

### Milestone 6 — Ground-lifted defect and varying-Hilbert strong-limit theorem

**Status: integrated conditionally on explicit convergence data.**

The ground-lifted defect removes the changing ground-sector bookkeeping by acting as identity on the finite ground sector and as `I - T` on excited/null modes.

For the actual finite `Z₂` system:

```text
(1/2) * ||f||^2 <= inner(D_H f, f)
```

on the whole finite carrier.

For every supplied asymptotically embedded strong-limit package, the repository proves:

```text
(1/2) * ||f||^2 <= inner(D_infinity f, f)
spectrum ℝ D_infinity ⊆ [1/2, infinity)
0 ∈ resolventSet ℝ D_infinity
||D_infinity^{-1}|| <= 2.
```

Still open:

```text
construct the actual approximation maps
construct the actual isometric embeddings
prove approximation convergence
prove evolved strong convergence
identify the resulting limit as a physical continuum operator.
```

### Milestone 7 — Projective-limit finite-marginal `L²` isometric system

**Status: integrated.**

For a projective-limit probability measure and finite coordinate sets `J ⊆ I`, the carrier constructs:

```text
tau[J,I] : L2(Q J) -> L2(Q I)
iota[J]   : L2(Q J) -> L2(mu)
```

as real-linear isometries with exact compatibility

```text
iota[J] = iota[I] after tau[J,I].
```

The continuum ranges are directed finite-coordinate cylinder subspaces.

### Milestone 8 — Cylinder density

**Status: integrated.**

The repository proves the correct topological exhaustion:

```text
topologicalClosure (sup_J cylinderSubspace(J)) = top.
```

It deliberately does not claim algebraic equality of the finite-cylinder supremum with the full `L²` carrier.

The proof uses finite-coordinate cylinders as a measurable generating set algebra and finite-measure `Lp` induction; no artificial countable skeleton is inserted.

### Milestone 9 — Compatible finite-marginal operator extension

**Status: integrated.**

A uniformly bounded compatible family is:

```text
conjugated to cylinder ranges
  -> proved compatible on arbitrary overlaps through I union J
  -> glued on the algebraic cylinder core
  -> bounded on that core
  -> extended to the complete continuum L2 carrier.
```

The extension has exact finite-marginal intertwining, common bounds, and uniqueness.

Still open:

```text
construct the actual compatible family from finite gauge geometry
prove the family approximates one physical evolution or defect
prove evolved convergence.
```

### Milestone 10 — Actual finite `Z₂` to selected projective-marginal bridge

**Status: theorem generator integrated; model-facing identification open.**

The actual finite Gauss-invariant Hilbert carrier is not unconditionally equated with an arbitrary marginal `L²` space. Instead the repository requests explicit data:

```text
selected finite coordinate set
mutually inverse real-linear isometries
actual defect realization on the selected marginal
compatible finite-marginal operator system.
```

Given those data, exact intertwining, symmetry, coercivity `1/2`, continuum embedding, and equality of embedded quadratic forms follow automatically.

The next goal is to construct these data canonically from the actual finite probability/gauge-orbit geometry.

### Milestone 11 — Concrete finite spectral-probability `L²` realization

**Status: integrated.**

The generic layer constructs strict finite-probability `L²` coordinates for any finite-dimensional real Hilbert space. An orthonormal diagonal operator becomes literal pointwise multiplication.

The actual `Z₂` specialization proves:

```text
canonical spectral-index finite probability
exact carrier isometry
pointwise ground-lifted defect coefficient
exact conjugacy and intertwining
exact diagonal quadratic form
symmetry
whole-carrier coercivity 1/2.
```

Boundary:

```text
the spectral-index probability is a coordinate realization
it is not yet the Euclidean finite marginal
it is not yet the residual gauge-orbit probability.
```

### Milestone 12 — Actual residual gauge-orbit probability `L²`

**Status: active; not integrated.**

Target package:

```text
finite group-action orbit quotient and Fintype
pushforward orbit-counting probability
strict positivity of every orbit mass
square-root-orbit-mass coordinates
isometric equivalence with invariant wavefunctions
actual residual slice-gauge orbit quotient
nontriviality of the actual orbit space
actual Gauss-invariant carrier = orbit-probability L2
actual ground-lifted defect on the orbit carrier
exact coercivity 1/2.
```

Draft PR #1409 contains a candidate implementation, but the roadmap does not mark this milestone complete without completed final-head CI and integration.

### Milestone 13 — Cross-volume orbit/marginal transition system

**Status: open; immediate frontier after Milestone 12.**

Required theorem unit:

```text
choose concrete finite coordinate/marginal spaces
  -> construct maps between finite gauge-orbit probability spaces
  -> prove measure preservation or the exact Radon--Nikodym correction
  -> construct L2 transition isometries
  -> prove compatibility with actual finite defects
  -> prove cocycle / directed-system laws
  -> identify these maps with projective finite-marginal transitions.
```

The transition system must be derived from actual gauge-field restriction/coarse-graining geometry, not supplied as an opaque family of isometries.

### Milestone 14 — Actual compatible continuum operator and convergence

**Status: open.**

Required chain:

```text
actual finite orbit/marginal operators
  -> uniform operator bound
  -> exact transition intertwining
  -> unique continuum L2 extension
  -> approximation maps into the common carrier
  -> strong convergence on the dense cylinder core
  -> whole-carrier strong convergence
  -> evolved convergence or resolvent convergence
  -> preservation of coercivity 1/2 by the actual limit.
```

A theorem conditional on supplied convergence data is already integrated; this milestone constructs and discharges those data.

### Milestone 15 — Thermodynamic and continuum scaling for the finite gauge model

**Status: open.**

Required choices and estimates:

```text
volume sequence
lattice-spacing sequence
coupling sequence
boundary and gauge-fixing conventions
uniform local regularity
tightness / projective consistency
control of the transfer normalization
compatibility of geometric time with the scaling trajectory.
```

A finite-volume common gap is necessary but not sufficient for a continuum theory.

### Milestone 16 — Compact `SU(2)` / `SU(N)` geometric extension

**Status: open.**

The current complete geometric full-gap theorem is for finite `Z₂`. The compact-Haar `SU(N)` Gibbs/heat-bath lane is substantial but does not yet contain the same actual adjacent-slice Perron--Doob coordinate-response closure.

Required work includes:

```text
compact temporal-link integration
compact residual-gauge orbit/marginal geometry
positive Perron or Krein--Rutman replacement
localized posterior response without finite-state shortcuts
volume-independent geometric transfer gap
compatible continuum scaling.
```

Finite `Z₂` must not be relabeled as compact `SU(2)` or `SU(N)` Yang--Mills.

### Milestone 17 — Continuum Euclidean Yang--Mills measure

**Status: open.**

Required outputs:

```text
nontrivial continuum probability measure
correct gauge content
Euclidean covariance
reflection positivity
clustering
regularity / temperedness
compatibility with the finite approximants.
```

The generic projective-limit machinery does not replace the construction and proof of these physical properties.

### Milestone 18 — OS reconstruction, physical Hamiltonian, and spectral transfer

**Status: theorem infrastructure integrated; concrete identification open.**

Required chain:

```text
continuum OS measure
  -> physical Hilbert space
  -> geometric time semigroup
  -> self-adjoint Hamiltonian
  -> identification with the continuum limit of finite geometric defects/transfers
  -> vacuum sector
  -> strict nonvacuum spectral lower bound.
```

The operator obtained from projective-limit `L²` extension is not automatically the OS-reconstructed Hamiltonian or its defect.

### Milestone 19 — Physical normalization and final claim

**Status: open.**

Required distinctions:

```text
finite transfer cap 1/2
finite defect coercivity 1/2
continuum transported coercivity
Hamiltonian energy gap
internal exactGapValueReal = 33/20
physical mass in fixed units.
```

A final theorem requires explicit maps and normalization theorems connecting these quantities. No numerical identity is inferred by notation or intention.

## Immediate proof packages

### Package A — Complete and validate the gauge-orbit probability realization

```text
generic orbit pushforward probability
  + invariant-wavefunction L2 isometry
  + actual residual gauge-orbit quotient
  + exact defect conjugacy
  + coercivity 1/2
  -> completed final-head CI and integration.
```

### Package B — Construct actual cross-volume maps

```text
finite gauge restriction/coarse-graining map
  -> orbit-map well-definedness
  -> pushforward/marginal law
  -> L2 pullback or corrected isometry
  -> defect/operator intertwining
  -> directed compatibility.
```

### Package C — Instantiate the projective-limit operator system

```text
actual finite orbit probability carriers
  + cross-volume transition isometries
  + actual defect compatibility
  + common norm bound
  -> compatible finite-marginal operator family
  -> unique bounded continuum L2 defect.
```

### Package D — Prove actual convergence

```text
dense cylinder-core convergence
  -> whole-carrier strong convergence
  -> evolved or resolvent convergence
  -> actual application of the ground-lifted strong-limit theorem
  -> continuum coercivity 1/2 and zero-resolvent package.
```

### Package E — Move from finite `Z₂` to physical compact gauge theory

```text
compact SU(2) / SU(N) one-slab geometry
  -> compact posterior response
  -> compact full-transfer gap
  -> physical scaling trajectory
  -> continuum Euclidean measure
  -> OS Hamiltonian and mass gap.
```

## Permanent anti-goals

The development must not:

```text
weaken theorem statements or physical assumptions to make a proof elaborate
count an open, Draft, stale, or unmerged PR as theorem authority
count queued or in-progress CI as success or failure
change code in response to an external Actions outage without a completed code failure
identify random-scan or heat-bath time with geometric one-slab time
promote total-variation contraction to L2 coercivity without an L2 theorem
confuse positive finite-volume gaps with a volume-uniform gap
confuse a transfer eigenvalue cap with a Hamiltonian energy in physical units
confuse the spectral-probability coordinate space with a Euclidean marginal
confuse a supplied finite-carrier isometry with a constructed gauge-geometric identification
confuse finite Z2 with compact SU(2) / SU(N) Yang--Mills
confuse projective-limit L2 operator extension with OS reconstruction
confuse exactGapValueReal = 33/20 with the finite constant 1/2
present 33/20 as a physical mass without unit and continuum-identification theorems
claim an unconditional Clay solution before the concrete continuum construction is closed.
```

## Completion criteria

### Finite `Z₂` geometric stage

**Completed.** It requires and now has:

```text
actual adjacent-slice transfer
Perron ground and spectral decomposition
common high-temperature interval
correct-marginal coupling
coordinate-resolved response
full-transfer spectral cap 1/2
full-transfer Dirichlet coercivity 1/2.
```

### Concrete finite carrier stage

Complete when:

```text
the actual residual gauge-orbit probability L2 realization is integrated
and its relation to the spectral-probability realization is explicit.
```

### Cross-volume projective stage

Complete when:

```text
actual finite orbit/marginal carriers form a directed compatible system
the actual defects intertwine under every transition
and the system instantiates the generic continuum operator extension.
```

### Continuum operator stage

Complete when:

```text
the actual finite family converges on the common continuum carrier
coercivity 1/2 is preserved by constructed—not merely supplied—convergence data
and the limit operator is identified with the relevant Euclidean/OS evolution object.
```

### Physical Yang--Mills stage

Complete only when:

```text
a compact nonabelian gauge model is constructed along a physical scaling trajectory
the continuum Euclidean measure and OS axioms are proved
the reconstructed Hamiltonian is identified
a strict physical spectral gap is proved
and physical-unit normalization is established.
```

## Replay baseline

```text
Lean:
  leanprover/lean4:v4.30.0-rc2

mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

The authoritative workflow remains exact-base Draft development, completed final-head validation, Ready re-audit, squash merge with fixed `expected_head_sha`, and post-merge identity verification.
