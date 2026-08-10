# MGAP4D Roadmap

This document records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

It separates:

- theorem infrastructure already integrated on the authoritative carrier;
- actual finite compact-Wilson and finite `Z₂` constructions;
- finite-to-continuum common-carrier and reverse-recovery theorem generators;
- current kinematic and dynamical model-facing obligations;
- the conditional R4 exact-value route; and
- claims that are explicitly not made.

## Snapshot — 2026-08-10 JST

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #1602
  Reduce independent OS classes to finite positive-definite Gram matrices

fixed integrated PR head:
  5d4c2d72a6aadd9f559efa9d8c0effade79189b9

latest authoritative carrier / squash integration:
  3816c7600477f613c1a16d2dd38f0c177d11649c

latest completed validation:
  PR Lean Fast Check #9923
  run id 31350112541
  job id 93339185437
  completed / success

terminal build:
  Build completed successfully (8744 jobs)

artifact:
  lean-fast-check-log
  id 9048695428
  sha256:c5b6896e86ffd9eec562e9fcb68418d588d6dee9e6b5df89247b83d478f94c74

post-merge comparison:
  3816c7600477f613c1a16d2dd38f0c177d11649c
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Open, Draft, stale, superseded, and closed-unmerged pull requests are not part of the authoritative theorem state.

## Current proof architecture

The repository now has seven main lanes.

```text
A. continuum OS / Hamiltonian / PVM

reflection positivity
  -> OS separated quotient
  -> real Hilbert completion
  -> symmetric contraction semigroup
  -> graph-closed physical Hamiltonian
  -> PVM / bounded-Borel calculus
  -> variational physical mass


B. actual compact SU(N) finite Wilson OS geometry

finite Wilson Gibbs law
  -> positive-time Wilson reflection form
  -> completed finite OS Hilbert H_n^OS
  -> boundary-Haar L2 realization
  -> interacting boundary marginal m_{0,n}^2 dHaar
  -> selected compact projective observation and boundary recovery


C. finite Z2 geometric-transfer theorem

actual adjacent-slice slab transfer
  -> Perron / Doob geometry
  -> exact-marginal coupling
  -> coordinate-response matrix
  -> full excited-transfer cap 1/2
  -> geometric Dirichlet coercivity 1/2
  -> conditional varying-Hilbert preservation


D. intrinsic finite Wilson rate and slow-state recovery

finite excitation operator norm
  -> intrinsic rate g_n
  -> positive two-step operator
  -> theorem-generated slow state phi_n
  -> continuum symmetric-semigroup time average
  -> moving Rayleigh limsup machinery
  -> selected two-step o(a_n) recovery interface


E. interacting common carrier across lattice scales

interacting boundary marginals mu_{partial,n}
  -> countable product probability
  -> finite OS isometries into common L2
  -> canonical common vacuum
  -> common-product-to-physical isometry
  -> mass-free finite-to-continuum ambient carrier


F. physical mass / R4 exact-value lane

forward intrinsic-rate comparison
  + reverse selected slow-state recovery
  -> conditional C.limit = physicalYangMillsMass

physical component forms
  -> component Rayleigh extrema
  -> R4 direct variational budget
  -> conditional normalized 33/20 endpoint


G. current continuum strictness reduction

common-product L2 separability
  -> infinite-dimensional physical Hilbert suffices
  -> vacuum-orthogonal orthonormal sequence
  -> independent separated OS classes
  -> finite positive-definite OS Gram matrices
  -> explicit strict continuum Wilson OS family [open]
```

## Current frontier at a glance

The immediate work is no longer to invent another abstract physical carrier. The repository has reduced the remaining model-facing obligations to concrete analytic statements.

```text
KINEMATIC FRONTIER

explicit countable positive-time gauge-invariant continuum observables
  -> finite reflected OS Gram matrices are positive definite
  -> global separated OS classes are linearly independent
  -> physical Hilbert is infinite-dimensional
  -> common-product physical isometry is theorem-generated
  -> all finite mass-free ambient embeddings are theorem-generated


DYNAMICAL FRONTIER

canonical finite Wilson slow states phi_n
  + theorem-generated finite/common embeddings
  -> prove
     ||iota_n(K_n^2 phi_n) - T(2a_n)iota_n(phi_n)||
       <= 2a_n delta_n,
     delta_n -> 0
  -> physicalYangMillsMass <= C.limit
  -> with forward direction, C.limit = physicalYangMillsMass


NUMERICAL / PHYSICAL-NORMALIZATION FRONTIER

actual R4 decomposition
  -> six component Rayleigh extrema
  -> sharp budget attainment
  -> independent physical referenceTime
  -> only then interpret a normalized 33/20 identity physically
```

## Milestone ledger

### Milestone 0 — Authority, replay, and claim discipline

**Status: integrated and permanent.**

Repository governance for the authoritative theorem carrier remains:

```text
start ordinary PRs from the exact canonical SHA
start as Draft
fix the final head before Ready
use only completed run / job / step / artifact / log evidence for CI conclusions
do not treat queued or in_progress as success or failure
do not write to a branch while its CI is running
separate Lean/code failures from GitHub Actions or external infrastructure failures
re-audit base, head, mergeability, reviews, threads, and overlapping PRs before Ready
re-audit again after Ready
squash merge only
fix expected_head_sha at merge
verify post-merge identical / ahead 0 / behind 0.
```

The public `main` branch is the repository landing surface, not the theorem authority. Documentation merged to the authoritative carrier must be synchronized separately to `main`.

### Milestone 1 — Continuum OS, Hilbert completion, semigroup, Hamiltonian, and PVM infrastructure

**Status: integrated as theorem infrastructure.**

Integrated surfaces include:

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
physical semigroup interfaces
strong-continuity and generator machinery
graph-closed Hamiltonian domain
symmetric / self-adjoint operator interfaces
PVM and bounded-Borel integration
scalar spectral measures and support
variational non-vacuum mass interfaces.
```

Boundary:

```text
the interacting continuum Yang--Mills construction itself is not thereby produced
a supplied continuum construction spine may carry stronger exact-spectrum data
internal exact-value theorem transport is not a substitute for model construction.
```

### Milestone 2 — Finite compact-Haar `SU(N)` Wilson Gibbs and heat-bath analysis

**Status: integrated.**

Integrated surfaces include:

```text
normalized finite periodic Wilson Gibbs probability
actual one-link conditional laws
compact Haar heat-bath kernels and projections
reversibility and Hilbert projection structure
conditional variance / Dirichlet identities
shared-plaquette localization
bounded-test Dobrushin control
finite Poincare/coercivity generators with genuine L2 input.
```

Permanent distinction:

```text
bounded-test or total-variation contraction
  !=
L2 spectral gap without a genuine Hilbert-space argument.
```

### Milestone 3 — Actual finite compact Wilson OS Hilbert completion

**Status: integrated.**

At each selected scale, the actual compact Wilson reflection form is carried through the OS quotient and completion. The completed finite carrier is not identified with an arbitrary raw probability `L²` space.

The canonical boundary-moment realization supplies

```text
H_n^OS ->_linear_isometry L2(boundary Haar_n).
```

This completed OS carrier is the finite Hilbert space used by the current intrinsic-rate and reverse-recovery lane.

### Milestone 4 — Interacting Wilson boundary marginal and density correction

**Status: integrated.**

The actual interacting reflection-fixed boundary law is

```text
d mu_{partial,n} = m_{0,n}^2 d mu_{Haar,n},
```

with strictly positive Wilson boundary vacuum moment `m_{0,n}`.

The repository constructs the reciprocal-vacuum density correction

```text
L2(boundary Haar_n)
  ->_linear_isometry L2(mu_{partial,n}).
```

Therefore the current interacting lane does not use the false beta-zero shortcut `boundary Gibbs = Haar` at nonzero coupling.

### Milestone 5 — Compact Wilson selected projective observation / boundary recovery

**Status: integrated as a theorem generator over concrete observation data.**

For one selected finite projective marginal at each scale, use:

```text
actual compact Wilson configuration
  -> selected finite projective observation
  -> measurable boundary readout
```

with exact pointwise compatibility with the actual Wilson boundary restriction.

`Measure.map_map` and the existing Wilson boundary pushforward theorem then generate the interacting boundary-marginal pushforward identity. The finite carrier becomes

```text
H_n^OS
  -> L2(boundary Haar_n)
  -> L2(mu_{partial,n})
  -> L2(selected projective marginal_n).
```

The finite OS space is identified with the exact range submodule of this embedding, not the whole marginal `L²` space.

### Milestone 6 — Finite `Z₂` geometric one-slab transfer and full gap

**Status: integrated.**

The finite even-four-torus `Z₂` prototype contains:

```text
actual adjacent-slice Wilson kernel
spatial half-action sandwich
temporal-link summation
residual Gauss projection
positive Perron ground
exact geometric Doob row
exact-marginal posterior coupling
coordinate-response matrix.
```

On one positive volume-independent high-temperature interval:

```text
all strictly excited normalized transfer eigenvalues <= 1/2
geometric Doob Dirichlet coercivity constant = 1/2.
```

This theorem is a completed finite geometric prototype. It does not identify finite `Z₂` with compact `SU(2)` / `SU(N)` continuum Yang--Mills.

### Milestone 7 — Ground-lifted defect and varying-Hilbert gap preservation

**Status: integrated conditionally on explicit convergence data.**

The finite `Z₂` full-transfer theorem yields a whole-carrier defect coercivity bound with constant `1/2`.

Given supplied varying-Hilbert approximation and evolved-convergence data, the repository preserves this exact coercivity at the limit and derives the corresponding real-spectrum and resolvent consequences.

Still required for a physical use of this theorem:

```text
construct the actual approximation maps
construct the actual embeddings
prove the actual convergence
identify the limit with the intended physical operator.
```

### Milestone 8 — Projective-limit `L²` cylinder system, density, and compatible-operator extension

**Status: integrated as generic infrastructure.**

The repository constructs:

```text
finite-marginal L2 pullback isometries
directed cylinder subspaces
topological density of their algebraic supremum
compatible operator gluing on the cylinder core
unique bounded continuum L2 extension.
```

This machinery remains available for physical finite-to-continuum constructions, but the current compact-Wilson common carrier no longer depends on pretending that interacting Gibbs laws at distinct lattice spacings form an exact projective family.

### Milestone 9 — Actual finite Wilson intrinsic logarithmic excitation rate

**Status: integrated.**

For the completed finite Wilson excitation operator,

```text
g_n = -log ||T_n^exc|| / a_n.
```

The finite rate is obtained from the actual operator norm; no finite-dimensional eigenvalue attainment is required.

The existing forward common-carrier theorem supplies the finite-to-continuum variational direction once its mass-free carrier hypotheses are instantiated.

### Milestone 10 — Positive two-step Wilson slow-state construction

**Status: integrated.**

For every bounded symmetric finite excitation operator, Mathlib adjoint identities prove positivity of the square and the exact norm identity

```text
||T^2|| = ||T||^2.
```

This yields a two-step Rayleigh/log-rate recovery theorem without a one-step positivity assumption.

For the actual finite Wilson operator, the repository theorem-generates unit slow states at every scale. A canonical selected state `phi_n` can be chosen with finite two-step energy below

```text
g_n + a_n.
```

### Milestone 11 — Symmetric-semigroup time-domain Rayleigh recovery machinery

**Status: integrated.**

The generic continuum side now avoids an unnecessary spectral recovery assumption.

Integrated chain:

```text
symmetric contraction semigroup correlations
  -> positive and commuting semigroup defects
  -> triple-defect factorization
  -> pairwise trapezoid inequality
  -> lossless interval-integrated numerator bound
  -> time-average denominator lower bound
  -> graph-domain generator identity
  -> moving Rayleigh correction.
```

For unit input and `2 h d_h < 1`,

```text
R(A_h psi) <= d_h / (1 - 2 h d_h).
```

If `h_n -> 0` and scalar dominators converge to `L`, the correction also converges to `L` and denominator positivity is eventually automatic.

### Milestone 12 — Scalar and vector reverse Wilson mass recovery

**Status: theorem generators integrated.**

The scalar route uses theorem-generated finite slow states plus a mass-free one-sided scalar compatibility to prove

```text
physicalYangMillsMass <= C.limit.
```

The vector route reduces that scalar compatibility to

```text
||iota_n(T_n^2 phi) - T(2a_n)iota_n(phi)||
  <= 2a_n delta_n,
delta_n -> 0,
```

using real Cauchy--Schwarz and exact norm preservation.

It also theorem-generates a genuine nonzero vacuum-orthogonal graph-domain continuum excitation witness.

Boundary:

```text
the vector residual is not yet derived from the bare compact Wilson / continuum model.
```

### Milestone 13 — Selected slow-state Mosco/Gamma-limsup reduction

**Status: integrated; actual residual proof open.**

The reverse dynamical obligation is no longer imposed on all finite unit excitations. It is sufficient to prove the moving-time two-step residual only for the canonical theorem-generated slow-state sequence `phi_n`:

```text
||iota_n(K_n^2 phi_n) - T(2a_n)iota_n(phi_n)||
  <= 2a_n delta_n,
delta_n -> 0.
```

Given this residual and the mass-free ambient carrier, the repository proves the reverse physical mass inequality and continuum excitation witness.

**This selected residual is one of the two principal current open obligations.**

### Milestone 14 — Interacting boundary common product across Wilson scales

**Status: integrated.**

Instead of asserting exact projectivity of interacting Wilson measures across lattice spacings, construct the countable product

```text
mu_common = product_n mu_{partial,n}.
```

For every scale,

```text
H_n^OS
  -> L2(boundary Haar_n)
  -> L2(mu_{partial,n})
  -> L2(mu_common)
```

is a genuine linear isometry.

This gives one mass-free common kinematic Hilbert carrier without a false cross-scale Gibbs consistency assumption.

### Milestone 15 — Canonical common vacuum

**Status: integrated.**

The coherent positive-half Wilson pullback initially has a scale-wise sign ambiguity. The repository proves from its exact reflected quadratic identity on the unit observable that the unit image is a constant sign `s_n` with

```text
s_n^2 = 1.
```

Multiplying the entire positive-half pullback by that sign preserves every reflected quadratic observable and selects the canonical `+1` branch.

Consequently the finite OS vacuum is theorem-generated to the constant-one vector in every interacting boundary marginal and then in the common product.

No extra scale-wise vacuum normalization field is required.

### Milestone 16 — One common-product physical isometry generates the mass-free ambient carrier

**Status: integrated as a theorem generator; concrete realization reduced further downstream.**

A single vacuum-preserving linear isometry

```text
L2(mu_common) -> P.PhysicalHilbert
```

generates every finite scale map

```text
H_n^OS -> P.PhysicalHilbert,
```

with exact norm and vacuum preservation, and therefore generates the entire mass-free ambient carrier used by the reverse recovery theorem.

The repository then systematically removes this map as an opaque input in Milestones 17--20.

### Milestone 17 — Hilbert-basis / dimension / cardinal reductions

**Status: integrated.**

The common-product physical isometry can be generated from progressively weaker Hilbert geometry:

```text
explicit Hilbert bases + vacuum-compatible index embedding
  -> theorem-generated vacuum-containing Hilbert bases + one index embedding
  -> lifted Hilbert-cardinal inequality.
```

These layers are retained as reusable generic Mathlib infrastructure, but are no longer the preferred final model-facing interface.

### Milestone 18 — Separable common product + infinite-dimensional physical Hilbert

**Status: integrated.**

The actual interacting common-product `L²` is proved separable from the measure-theoretic topology and finite exponent facts.

For a complete real Hilbert target with unit vacuum, Mathlib Hilbert-basis extension shows that

```text
not FiniteDimensional physicalHilbert
```

produces an `ℕ`-indexed orthonormal sequence orthogonal to the vacuum. Separability of the common-product source then gives a vacuum-preserving common-product-to-physical isometry.

Thus the kinematic obligation is reduced from a Hilbert-cardinal statement to physical-Hilbert infinite-dimensionality.

### Milestone 19 — Infinite-dimensionality reduced to independent separated OS classes

**Status: integrated.**

It is sufficient to construct

```text
observable : ℕ -> P.Carrier
```

of positive-time gauge-invariant continuum observables whose separated OS classes are linearly independent.

An infinite linearly independent family makes the separated pre-Hilbert space non-finite-dimensional. Injectivity of the canonical completion map prevents its Hilbert completion from becoming finite-dimensional.

This theorem-generates Milestone 18 and hence the common-product physical carrier.

### Milestone 20 — Independent OS classes reduced to finite positive-definite Gram matrices

**Status: integrated — latest checkpoint #1602.**

Mathlib provides the finite-local characterization of linear independence and the theorem that a positive-definite Gram matrix implies linear independence.

The resulting generic equivalence is:

```text
(for every finite s, Gram(v restricted to s) is positive definite)
  <->
LinearIndependent v.
```

For the actual continuum OS carrier, it is therefore sufficient to prove that every finite matrix

```text
G_ij = D.osBilinForm P.omega
         (P.toPositiveTime (observable i))
         (P.toPositiveTime (observable j))
```

is positive definite.

Reflection positivity alone gives positive semidefiniteness, not the strict inequality required for `Matrix.PosDef`.

### Milestone 21 — Concrete strict continuum OS nondegeneracy

**Status: open — immediate kinematic frontier.**

Required theorem unit:

```text
choose an explicit countable family of positive-time
continuum gauge-invariant Wilson/OS observables

  -> compute or control every finite reflected OS Gram matrix
  -> prove strict positivity for every nonzero finite coefficient vector
  -> package Matrix.PosDef for every finite subfamily
  -> invoke #1602
  -> theorem-generate the common-product physical carrier
  -> theorem-generate all finite-to-continuum ambient embeddings.
```

Important restriction:

```text
OS reflection positivity alone is insufficient:
it yields semidefinite Gram matrices.
The missing statement is strict nondegeneracy for one concrete infinite family.
```

This should be attacked from actual continuum Wilson correlation structure, locality/separation, or another model-derived strictness theorem, not inserted as a renamed Hilbert-dimension certificate.

### Milestone 22 — Prove the selected slow-state moving-time residual

**Status: open — immediate dynamical frontier.**

With Milestone 21 supplying the kinematic ambient carrier, prove for the canonical finite slow states:

```text
||iota_n(K_n^2 phi_n) - T(2a_n)iota_n(phi_n)||
  = o(a_n).
```

Equivalent proof-relevant form:

```text
exists delta_n -> 0 such that
||iota_n(K_n^2 phi_n) - T(2a_n)iota_n(phi_n)||
  <= 2a_n delta_n.
```

Desired sources of this estimate include actual common-carrier semigroup comparison, quantitative finite-to-continuum transfer convergence, or an appropriate Mosco/Trotter--Kato style theorem specialized to the selected recovery sequence.

Do **not** replace it by fixed-time convergence without a rate argument.

### Milestone 23 — Actual physical mass equality

**Status: theorem route integrated; concrete closure depends on Milestones 21 and 22.**

The repository already contains the two variational directions needed for the intrinsic rate.

Once the current actual carrier and selected recovery residual are constructed, theorem composition gives

```text
C.limit = physicalYangMillsMass.
```

The route does not require a separately supplied positive mass certificate, a convergent sequence of exact finite eigenvectors, or a legacy finite gap-certificate owner.

This equality is not advertised as unconditionally discharged before the model-facing hypotheses are constructed.

### Milestone 24 — Actual R4 decomposition and component variational extrema

**Status: structural variational layer integrated; numerical evaluations open.**

For every actual component quadratic form `q`, the canonical coefficient is identified with the genuine Rayleigh extremum:

```text
lower coefficient = sInf componentRayleighSet(q)
upper coefficient = sSup componentRayleighSet(q).
```

The direct R4 budget is therefore built from actual physical graph-domain states, not arbitrary coefficient certificates.

Open work:

```text
derive the final six-component decomposition from the actual model
prove form boundedness and the required domains where not already generated
evaluate the six actual extrema
prove the sharp combined budget is attained, or prove equivalent sharpness.
```

### Milestone 25 — Conditional `33/20` normalized endpoint

**Status: theorem assembly integrated; physical derivation open.**

If the six actual component extrema are proved to be

```text
9/5, 1/10, 0, 1/10, 1/20, 1/10,
```

and the direct R4 budget is sharply attained, the structural theorem gives the normalized sum `33/20`.

With actual physical mass equality and an independently constructed `referenceTime`, the intended endpoint takes the form

```text
referenceTime * physicalYangMillsMass = 33/20.
```

Still open:

```text
the six model-derived extrema
their physical decomposition provenance
sharp budget attainment
independent reference-time / physical-unit normalization.
```

The repository must not set any of these inputs merely to obtain the target rational number.

### Milestone 26 — Interacting continuum Yang--Mills construction

**Status: open.**

The generic and conditional continuum theorem infrastructure does not replace the physical construction.

Required output includes a nontrivial interacting continuum gauge theory with the needed properties, including as appropriate:

```text
continuum probability / state construction
gauge content and covariance
reflection positivity
regularity / temperedness
clustering or vacuum uniqueness inputs
compatibility with the finite Wilson approximants
physical time semigroup identification.
```

Where the repository currently starts from supplied continuum OS data, those fields must ultimately be justified from the actual model rather than retained as terminal assumptions.

### Milestone 27 — Final physical Hamiltonian and mass-gap claim

**Status: open.**

The final physical claim requires all prior distinctions to be preserved:

```text
finite Z2 transfer cap 1/2
  != finite compact-Wilson intrinsic rate
  != continuum defect coercivity
  != physical Hamiltonian mass
  != normalized exact-value constant 33/20.
```

A final theorem must arise from the actual interacting continuum model, identify the reconstructed physical Hamiltonian, prove a strict non-vacuum spectral lower bound, and only then attach an independently derived physical normalization.

## Two principal current proof packages

The next development should prioritize two mathematically substantive packages rather than adding helper-only wrappers.

### Package A — Strict OS Gram construction

Target:

```text
actual continuum positive-time Wilson observables
  -> finite Gram strict positivity
  -> #1602 finite PosDef interface
  -> physical Hilbert infinite-dimensionality
  -> common-product physical carrier
  -> mass-free ambient carrier.
```

Preferred style:

```text
generic Mathlib strict-Gram helper only when genuinely reusable
then immediate actual continuum Wilson/OS specialization.
```

### Package B — Selected slow-state moving-time convergence

Target:

```text
actual finite Wilson selected slow state phi_n
  -> quantitative two-step finite/common comparison
  -> o(a_n) residual
  -> reverse variational inequality
  -> actual intrinsic-rate / physical-mass equality.
```

Preferred style:

```text
prove only the selected-sequence estimate actually needed by the limsup theorem;
do not reintroduce stronger all-vector or all-time assumptions.
```

The two packages are logically distinct: Package A closes the kinematic common carrier; Package B closes the dynamical recovery.

## Anti-goals and permanent distinctions

Do not:

- identify finite `Z₂` with compact `SU(2)` / `SU(N)` Yang--Mills;
- call the finite `Z₂` constant `1/2` the physical Yang--Mills mass;
- identify interacting Wilson boundary marginals with Haar at nonzero coupling;
- assert exact projectivity of interacting Wilson Gibbs laws across lattice spacings without an actual theorem;
- identify a completed finite OS Hilbert space with a whole raw marginal `L²` space when only a range identification is proved;
- turn reflection-positive semidefinite Gram matrices into positive-definite matrices without a strictness proof;
- replace the selected moving-time `o(a_n)` residual by ordinary fixed-time convergence;
- assume exact finite eigenvectors or norm attainment when operator-norm approximation suffices;
- insert a physical mass, exact spectrum vector, or legacy gap certificate into a kinematic common carrier;
- set R4 coefficients to the desired rational values instead of proving their actual variational extrema;
- set `referenceTime` to manufacture `33/20`;
- present `exactGapValueReal = 33/20` as a currently derived physical mass;
- claim a Clay Millennium solution before the interacting continuum construction and all model-facing obligations are discharged.

## Definition of completion for the present program

The current program is complete only when one theorem chain starts from actual interacting Yang--Mills/Wilson model data and constructs, rather than assumes:

```text
finite Wilson approximants
+ continuum OS model
+ strict OS nondegeneracy / common carrier
+ selected moving-time recovery
+ intrinsic finite-to-continuum mass equality
+ actual R4 decomposition and extrema
+ independent physical normalization
```

and then concludes the intended physical spectral statement without circular numerical input.

Until then, the repository should continue to distinguish theorem infrastructure, theorem generators conditional on explicit model-facing data, and genuinely discharged physical construction steps.
