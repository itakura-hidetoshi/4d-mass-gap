# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository deliberately separates three things:

1. formal theorem infrastructure that is already integrated;
2. model-specific theorem generators whose remaining hypotheses are explicit; and
3. physical construction obligations that are still open.

It does **not** currently claim an unconditional construction of interacting four-dimensional continuum Yang--Mills theory, and it does **not** claim a proof of the Clay Millennium problem.

## Repository status — 2026-08-15 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Current authoritative head:
  7fb099ddc94275f0b0832d98aefc25bc5a699196

Latest integrated checkpoint:
  PR #1669
  Lift full positive-boundary Wilson Fock strictness to the actual analysis sector

Active development Draft:
  PR #1670
  Lift actual Wilson strictness to a reconstructed physical excitation

Active Draft branch:
  formal/actual-wilson-os-physical-excitation-v1

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. Draft and open PR results are reported separately below so that current progress is visible without confusing it with the integrated baseline.

## Where the proof stands now

The current proof spine is best summarized as follows.

```text
actual periodic-even compact Wilson Gibbs model
  -> finite reflection positivity and OS completion
  -> boundary-Haar / interacting-boundary L2 realizations
  -> positive-boundary Wilson Fock / Gram strictness
  -> actual Wilson boundary analysis nonzero and centered modes
  -> actual plaquette-algebra C0 closure                    [Draft #1670]
  -> coherent positive-time pullback / L2 range bridges   [Draft #1670]
  -> reconstructed nonzero vacuum-orthogonal excitation   [downstream theorem route]
  -> Hamiltonian-domain / Rayleigh / physical-mass interfaces
```

The decisive change since the earlier documentation is that the immediate active frontier is no longer the generic reduction from continuum OS linear independence to finite positive-definite Gram matrices. That generic reduction remains useful infrastructure, but the actual finite Wilson construction has moved much further downstream.

The latest integrated checkpoint, PR #1669, reaches **actual finite Wilson strictness in the actual-analysis sector**. The active Draft #1670 then develops the missing finite-Wilson-to-positive-time realization layer.

## Integrated theorem spine

### 1. Continuum OS, Hilbert completion, semigroup, Hamiltonian, and PVM infrastructure

The repository contains formal infrastructure for

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
symmetric contraction semigroups
strong continuity and generator-domain machinery
graph-closed physical Hamiltonians
self-adjoint / symmetric operator interfaces
PVM and bounded-Borel spectral calculus
scalar spectral measures and support theorems
variational non-vacuum physical-mass interfaces.
```

These theorems transport consequences from supplied continuum construction data. They do not by themselves construct the interacting continuum Yang--Mills model.

### 2. Actual finite compact `SU(N)` Wilson / OS geometry

The finite compact-gauge lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure and contains actual periodic Wilson Gibbs laws, reflection-positive finite OS forms, completed finite OS Hilbert carriers, boundary-moment representations, interacting boundary marginals, and density-corrected `L²` transports.

The interacting reflection-fixed boundary law is treated as

```text
d mu_{partial,n} = m_{0,n}^2 d mu_{Haar,n},
```

not as Haar measure at nonzero coupling.

### 3. Finite `Z₂` geometric-transfer theorem

The finite even-four-torus `Z₂` lane proves a genuine geometric transfer result with

```text
strictly excited normalized transfer eigenvalues <= 1/2
geometric Doob Dirichlet coercivity constant = 1/2
```

on a positive volume-independent high-temperature interval.

This is a finite `Z₂` theorem. It is **not** the physical compact `SU(2)` / `SU(N)` Yang--Mills mass and is not the normalized exact-value constant `33/20`.

### 4. Intrinsic Wilson rates and reverse variational recovery machinery

For the completed finite Wilson excitation operator the repository defines the intrinsic logarithmic rate

```text
g_n = -log ||T_n^exc|| / a_n.
```

Mathlib positivity of the two-step operator and the identity `||T^2|| = ||T||^2` generate canonical finite slow states. The continuum symmetric-semigroup layer supplies time averaging, graph-domain generator identities, and a lossless moving Rayleigh estimate.

The reverse mass route is reduced to a selected theorem-generated slow-state sequence and a quantitative moving-time residual rather than all-vector convergence.

### 5. Common interacting boundary carrier and kinematic reductions

The repository constructs the countable product of interacting boundary marginals and canonical finite OS embeddings into a common `L²` carrier. It also contains generic reductions from a common-product physical isometry to physical Hilbert infinite-dimensionality, independent separated OS classes, and finite positive-definite reflected OS Gram matrices.

That global kinematic lane remains valid, but it is no longer the only route being developed toward a concrete physical excitation.

### 6. PR #1669 — actual positive-boundary Wilson strictness reaches actual analysis

The current authoritative head integrates the actual positive-boundary Wilson/Fock strictness package through the actual-analysis sector. Among the integrated consequences are:

```text
full positive-boundary temporal Wilson factorization
protected strict finite Wilson Gram structure
nonzero actual Wilson boundary analysis operator
inverse interacting-boundary L2 density transport
positive-density normalized-trace witnesses
actual open-half dual-probe nonzero results
factorized nonzero criteria for actual analysis
Hilbert-Schmidt / Gram factorization and convergence
strict centered actual-analysis output infrastructure.
```

This is the current integrated launch point for the active positive-time realization work.

## Active Draft #1670 — actual Wilson analysis to positive-time physical realization

PR #1670 is **not yet authoritative**, but it now contains a substantial theorem chain.

### A. Actual plaquette algebra and `C⁰` closure

A concrete actual finite plaquette algebra is constructed on the positive open-half configuration space. The raw normalized-trace-polynomial actual-analysis representative is proved to belong to the uniform closure of its bounded-continuous carrier:

```text
g_raw ∈ closure(actualPlaquetteAlgebraBoundedCarrier).
```

The proof is generated from actual finite plaquette/Wilson data, completed-positive Gram-feature continuity, polynomial approximation of Gibbs factors, and the boundary Bochner integral. No abstract `Dense` hypothesis is used for this target-specific approximation theorem.

### B. Canonical `C⁰ -> L²` transport

On the compact open-half configuration space, the raw continuous representative is transported through Mathlib's canonical

```lean
BoundedContinuousFunction.toLp
```

map to the already-used open-half Haar `L²` actual-analysis vector. Thus the analytic frontier is no longer basic `L²` construction; it is positive-time realizability of the finite continuous observables.

### C. OS carrier wrapper removed from the range problem

The finite OS carrier is proved canonically linearly equivalent to the physical positive-time submodule. Consequently the carrier-level positive-half `L²` map and the direct positive-time-submodule `L²` map have the same range.

This removes an opaque wrapper from the remaining realization statement without asserting any surjectivity of the finite Wilson pullback.

### D. Finite-positive-half observable range identified exactly

The actual finite positive-half observable image is proved equal to the range of the coherent positive-half pullback:

```text
range(finitePositiveHalfObservable_n)
  = range(Q.positiveHalfPullback n).
```

The reverse inclusion uses the canonical OS-carrier representative of a physical positive-time observable. It is not a statement that `Q.positiveHalfPullback n` is onto every bounded continuous open-half function.

### E. Normalized-trace-power readout is only packaging

The normalized-trace-power readout structure is reduced to concrete finite range membership. At one finite scale:

```text
Nonempty(normalizedTracePowerPositiveTimeReadout Q n)
  <->
for every j,
  rawTracePowerBoundedFunction(n,j)
    ∈ range(finitePositiveHalfObservable_n).
```

So the readout record is not an additional physical assumption. It is reusable packaging of actual finite Wilson realizability.

### F. Downstream physical excitation theorems are ready

Once the remaining positive-time realization statement is supplied, the existing Draft chain transports the raw actual-analysis mode through positive-time `L²`, produces a nonzero vacuum-orthogonal reconstructed state, reaches the physical Hamiltonian domain under the existing semigroup/self-adjointness hypotheses, and feeds the established Rayleigh / physical-mass interfaces.

No duplicate physical Hilbert space is introduced, and the static Wilson Gram operator `A†A` is not identified with Euclidean time evolution.

## Immediate local frontier

The cleanest closure-form frontier currently exposed by #1670 is

```text
periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
    (halfExtent n)
  ⊆
LinearMap.range (Q.positiveHalfPullback n).
```

Combined with the theorem-generated `C⁰` closure, this gives

```text
g_raw ∈ closure(range(Q.positiveHalfPullback n))
```

and hence the open-half Haar `L²` range-closure statement used by the physical-excitation route.

A complementary, more target-specific exact-range frontier is:

```text
for every normalized trace power j,
  rawTracePowerBoundedFunction(n,j)
    ∈ range(finitePositiveHalfObservable_n).
```

The desired next proof should construct these positive-time observables from the **existing projective/cylinder finite-Wilson geometry**. It should not obtain them by inserting any of the following stronger assumptions:

```text
global surjectivity of Q.positiveHalfPullback
global multiplicativity of Q.positiveHalfPullback
an abstract dense carrier assumption
a duplicate Hilbert carrier
an identification of static A†A with time translation.
```

Because `Q.positiveHalfPullback` is consumed downstream as a linear map, multiplication should be handled in the actual cylinder/observable construction itself, with pointwise readout compatibility proved before passing to the pullback range. Global multiplicativity must not be silently inferred.

## Program-level open obligations

The active local frontier above is only one part of the full Yang--Mills program. The major remaining obligations are:

### 1. Actual positive-time realization

Discharge the actual-plaquette-algebra lift or the target-specific normalized-trace-power finite-range family from concrete finite Wilson/projective/cylinder observables.

### 2. Selected moving-time recovery

For the canonical finite Wilson slow states `phi_n`, prove the genuine quantitative residual

```text
|| iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

Ordinary fixed-time convergence is not a substitute for this `o(a_n)` statement.

### 3. Global continuum/common-carrier realization

The earlier strict-Gram reduction remains a separate global route. If that route is used to generate the common-product physical isometry, one still needs a concrete countable continuum positive-time observable family with strictly positive finite OS Gram matrices.

The local #1670 excitation route does not by itself assert global infinite-dimensionality or automatically solve every common-carrier obligation.

### 4. Interacting continuum Yang--Mills construction

The actual continuum probability/state, gauge covariance, reflection positivity, regularity, clustering/vacuum properties, finite-Wilson compatibility, and physical time-semigroup identification must ultimately be generated from the model rather than retained as terminal data.

### 5. Physical exact-value normalization

The repository retains an exact normalized R4 theorem route involving `33/20`, but the physical interpretation still requires model-derived component extrema, sharpness, actual mass identification, and an independently constructed physical reference-time normalization.

## Numerical discipline

Three numerical surfaces must remain distinct.

```text
1/2
  finite high-temperature Z2 geometric-transfer spectral cap /
  finite geometric Dirichlet coercivity constant

33/20
  normalized exact-value endpoint in the R4 theorem route,
  conditional on additional model-specific variational and scale inputs

physicalYangMillsMass
  variational mass of the reconstructed physical Hamiltonian
```

The repository does not identify these constants merely because they appear in the same overall program.

## Key files around the current frontier

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean
  PeriodicHypercubicEvenBoundaryRawActualAnalysisPlaquetteAlgebraClosure.lean
  PhysicalYangMillsWilsonSU2ActualPlaquetteAlgebraPositiveTimeBridge.lean
  PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure.lean
  PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure.lean
  PhysicalYangMillsWilsonSU2FinitePositiveHalfObservableRangeBridge.lean
  PhysicalYangMillsWilsonSU2NormalizedTracePowerFinitePositiveHalfObservableBridge.lean
  PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout.lean
  PhysicalYangMillsWilsonSU2NormalizedTracePowerFiniteReadoutEquivalence.lean
  PhysicalYangMillsWilsonSU2RawActualAnalysisPhysicalExcitation.lean
  PhysicalYangMillsWilsonSU2RawActualAnalysisExcitationDomainWitness.lean
  PhysicalYangMillsWilsonSU2RawActualAnalysisDerivedRayleighMass.lean
```

## Validation and repository discipline

The authoritative development workflow is intentionally conservative:

```text
ordinary PRs start from the exact authoritative SHA and begin as Draft
CI conclusions use completed run / job / step / artifact / log evidence only
queued or in_progress runs are not treated as final evidence
do not add commits to a branch while its CI is running
separate Lean/code failures from Actions/cache/external failures
fix the final head before Ready
re-audit base/head/mergeability/reviews/threads before merge
squash merge only
pin expected_head_sha at merge
verify the authoritative branch after integration.
```

Typical local validation surfaces include `lake build` and the repository's changed-Lean fast-check scripts.

## Claim boundary

MGAP4D does **not** currently claim:

- an unconditional interacting four-dimensional continuum `SU(N)` Yang--Mills construction;
- a completed Clay Millennium mass-gap proof;
- that finite `Z₂` is the physical compact `SU(2)` / `SU(N)` theory;
- that finite coercivity `1/2` is the physical Yang--Mills mass;
- that the coherent positive-half pullback is globally surjective or multiplicative;
- that the active #1670 positive-time realization frontier is already discharged;
- that fixed-time convergence proves the selected moving-time `o(a_n)` residual;
- that `33/20` has already been derived as a physical mass in fixed units.

The development principle remains:

```text
generic Mathlib theorem
  -> actual finite Wilson / plaquette / OS specialization
  -> explicit positive-time and finite-to-continuum realization
  -> continuum physical Hamiltonian theorem
  -> only then physical numerical normalization.
```

See `ROADMAP.md` for the current milestone order and completion criteria.
