# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Osterwalder--Schrader reconstruction, transfer operators, and the mass-gap problem.

The repository is deliberately strict about claim boundaries. It distinguishes

1. theorems derived from the actual finite periodic Wilson model;
2. same-root continuum / OS / Hamiltonian constructions obtained from those finite objects;
3. generic analytic and spectral implication machinery; and
4. model-facing compatibility statements that are still open and must be proved before a Clay-level theorem can be claimed.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The canonical branch now contains much more than the older finite-volume/Poincaré checkpoint: it includes a same-root scalar continuum OS reconstruction, a graph-closed self-adjoint Hamiltonian framework, completed finite transfer spectral and logarithmic-generator machinery, transfer/Wightman spectral-core bridge machinery, and an SU(2) exact-gap mode pipeline whose remaining model seam has been reduced to a selected-mode scalar Wilson matrix-coefficient identity plus explicit finite/common-time coherence.
>
> The remaining scalar identity is **not** currently proved from the raw Wilson one-slab kernel, and the selected scalar continuum process is still not the full four-dimensional continuum Yang--Mills field. Those boundaries are essential.

## Repository status — 2026-09-02 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical exact SHA at this documentation checkpoint:
  9bdd8906d9af8241a79a565d29cff8021681f817

Latest merged mathematical checkpoint represented here:
  PR #3151
  Reduce SU2 exact-gap seam to selected-mode matrix coefficients

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative proof status.

---

## Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> physical boundary and spatial-slice L² carriers
  -> normalized one-slab physical transfer
  -> completed pair-Hilbert transfer
  -> positivity / compact spectral support
  -> logarithmic transfer generator / resolvent / spectral-floor machinery

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson primary scalar readout
  -> rational-time path law
  -> same-root Prokhorov continuum law
  -> continuum reflection positivity
  -> fixed-slot OS Hilbert spaces
  -> directed-limit Hilbert carrier
  -> real strongly continuous contraction semigroup
  -> dense right generator
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. TRANSFER / WIGHTMAN SPECTRAL LANE

positive compact physical transfer
  -> intrinsic positive spectral support
  -> partially-defined logarithmic generator
  -> spectral-mode span as a genuine Mathlib operator core
  -> common-core / self-adjoint intertwining machinery
  -> transfer point energies <-> Wightman H|Ω⊥ point energies
  -> intrinsic spectral floor / attained mass-gap certificate machinery

D. SU(2) EXACT-GAP MODE LANE

normalized SU(2) one-slab physical mode f_n
  + normalized one-slab top mode ω_n
  -> selected endpoint-pair boundary vector
  -> completed finite Wilson boundary transfer
  -> finite OS time-one eigenmode
  -> common-carrier limit
  -> continuum OS time-one eigenmode
  -> graph-closed vacuum-orthogonal Hamiltonian mode
     at exactGapValueReal

E. CURRENT RAW-MODEL SEAM

literal one-slab Wilson kernel / Hilbert-Schmidt matrix coefficients
  -> selected-mode scalar pair matrix-coefficient identity          [OPEN NOW]
  -> explicit finite/common-time normalization coherence            [OPEN NOW]
  -> CompletedBoundaryTransferOneSlabPairWeakAtFor
  -> the already-integrated exact-gap mode chain

F. FULL CLAY-LEVEL COMPLETION

same-root scalar / transfer machinery
  -> sufficiently rich continuum 4D Yang--Mills field/state         [OPEN]
  -> complete Euclidean/gauge/regularity package                     [OPEN]
  -> model-derived OS/Wightman identification on the full carrier   [OPEN]
  -> positive spectral gap above the vacuum on that carrier          [OPEN]
  -> Clay-level existence + mass gap                                 [OPEN]
```

The immediate frontier is therefore no longer accurately described as simply “prove a generic shared-boundary Poincaré estimate.” That remains an important global lower-bound route, but the current exact-gap construction has pushed the concrete SU(2) realization problem much further upstream: the mode-specific post-boundary assumptions have been eliminated, and the remaining exact-mode interface is now a scalar one-slab Wilson matrix-coefficient theorem.

---

## 1. Actual finite compact `SU(N)` Wilson root

The finite model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical finite-model infrastructure includes, among other components,

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
physical spatial-slice Haar-L² carriers
boundary Haar-L² carriers
normalized one-slab transfer operators
physical excitation-pair Hilbert completion
compactness / self-adjointness / positivity of the completed transfer lane
```

The interacting boundary law is not silently replaced by Haar measure at nonzero coupling.

---

## 2. Same-root scalar continuum OS construction

The constructive continuum OS lane currently uses a selected primary gauge-invariant scalar process, schematically

```text
ℚ -> ℝ.
```

It is obtained from actual finite Wilson pushforwards and therefore provides a genuine same-root continuum observable law. It is **not** the full continuum gauge connection on `ℝ⁴`.

The integrated route includes

```text
primary positive-half locality
reflection-completed rational-time paths
canonical scalar Wilson readout
tightness / Prokhorov subsequence
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completion
directed-system Hilbert construction
completed direct-limit carrier
```

Reflection positivity is transported from the finite Wilson model rather than inserted as an unrelated final axiom.

---

## 3. Real OS semigroup, Hamiltonian, and vacuum

The canonical OS reconstruction contains a real strongly continuous contraction semigroup on the regular sector.

Integrated analytic structure includes

```text
rational-time contraction and semigroup laws
NNRat -> NNReal orbit extension
real C₀ contraction semigroup
right difference-quotient generator
H_OS = -A_OS
dense generator domain
graph closure as a Mathlib LinearPMap
positive resolvents and Yosida approximation
self-adjoint graph-closed Hamiltonian
exact generator / closed-Hamiltonian identification
```

The literal constant-one cylinder gives the vacuum `Ω`, with canonical statements of the form

```text
‖Ω‖ = 1
T_t Ω = Ω
H Ω = 0.
```

The vacuum-orthogonal carrier `Ω⊥` is complete and invariant under the relevant semigroup/Hamiltonian structure.

A Hamiltonian carrier by itself is not yet a proof of a Yang--Mills mass gap; the model-derived spectral statement still has to be connected to the full physical theory.

---

## 4. Completed physical transfer and logarithmic spectral machinery

Since the older README checkpoint, the finite transfer lane has been developed far beyond a bare Poincaré interface.

The canonical branch now contains a substantial real-Hilbert spectral analysis of the completed physical transfer, including

```text
completed pair-transfer construction
self-adjoint contraction structure
positivity from finite tensor / Schur-product arguments
compact positive spectral support
transfer/generator spectral relations
below-gap and above-one resolvent calculus
all-order scalar resolvent derivative hierarchies
support logarithmic generator on the strictly-positive spectrum
spectral-mode eigenvector/domain theorems
intrinsic logarithmic spectral floor
effective-energy / resolvent-moment variational identifications
```

This machinery keeps the forward logarithmic generator partially defined where mathematically necessary rather than replacing an unbounded object by an artificial everywhere-defined operator.

---

## 5. Transfer-to-Wightman bridge: what is integrated

The repository also contains a layered transfer/Wightman bridge architecture.

The generic hard input was successively reduced from a global Hilbert equivalence and all-domain operator intertwining to common-core data, and then further to the canonical algebraic span of actual positive-transfer spectral modes.

Integrated mathematical reductions include

```text
two dense isometric core realizations -> canonical Hilbert equivalence
closed-subspace corestriction
Mathlib LinearPMap.HasCore closure transfer
self-adjoint maximality
canonical positive-transfer spectral span as a source operator core
mode-wise logarithmic-generator action
mode-wise target Hamiltonian action -> common-core action
common-core action -> full operator intertwining
point-energy-set transport
spectral-floor / Wightman mass-gap certificate implications
```

These theorems make the logical dependencies precise. They do not by themselves prove that every required Wightman realization equation comes from the raw finite Wilson model.

---

## 6. SU(2) exact-gap lane

A separate, highly tightened SU(2) lane now carries the repository's symbolic exact-gap value.

The public quantities include

```text
exactGapClusterContractionRatio = exp (-exactGapValueReal)
```

and the canonical analytic chain proves that, once the required finite model realization is supplied, the corresponding continuum OS time-one eigenvalue produces a graph-closed vacuum-orthogonal Hamiltonian mode with energy

```text
exactGapValueReal.
```

Recent canonical reductions removed several earlier opaque assumptions:

```text
boundary-image membership
  -> canonical Wilson boundary-moment closure

positive-time closure
  -> completed finite transfer graph equality

mode-specific post-synthesis closure
  -> one completed-boundary transfer equation

completed-boundary transfer equation
  -> pair-coordinate one-slab intertwining

strong pair intertwining
  -> weak matrix coefficients

all endpoint pairs
  -> one selected physical mode f_n paired with the normalized top mode ω_n
```

At PR #3151 the exact-gap lane therefore no longer needs an all-input operator equality. It needs only the weak scalar compatibility for the selected pair at each cutoff.

---

## 7. The immediate frontier after PR #3151

For one cutoff `n`, selected physical mode `f`, and normalized one-slab top mode `omega`, the canonical predicate

```lean
CompletedBoundaryTransferOneSlabPairWeakAtFor Q hInvariant C n f omega
```

requires equality of real pair-Haar `L²` matrix coefficients against every test vector `z` between

1. the completed OS boundary transfer, conjugated into ordered spatial-slice pair coordinates; and
2. the external tensor obtained by applying the normalized physical one-slab transfer to both endpoints.

Hilbert-space separation and the already-canonical inverse boundary/pair isometries then recover the exact vector equation. For SU(2), fixing `omega` to the normalized top mode yields the equation consumed by the finite OS exact-gap theorem.

### What is still missing

The remaining theorem must be derived from the **literal finite Wilson one-slab model**. In practical terms the next proof should connect

```text
translated / synthesized OS scalar matrix coefficient
```

to

```text
normalized one-slab Wilson kernel matrix coefficient
```

using the existing finite temporal translation, Wilson Gibbs invariance, boundary/slice identifications, Fubini/Hilbert-Schmidt kernel formulas, and the actual one-slab normalization.

There is also a separate time-normalization issue that must remain explicit: the abstract common semigroup family uses `C.translate 1`, while the finite lattice translation machinery has a cutoff-dependent physical lattice time. The current structures do **not** silently identify these two notions. The required finite/common-time coherence must be proved rather than assumed by definitional equality.

This is the present model-facing exact-mode frontier.

---

## 8. Scale-uniform Poincaré / coercive lane remains important

The older boundary `L²` Poincaré route has not been discarded. It remains a useful route for a **global vacuum-orthogonal lower bound**, rather than merely producing one selected exact mode.

The canonical implication machinery can consume estimates schematically of the form

```text
(1 - exp(-m t)) * ‖v‖²
  <= ‖v‖² - ‖K_(n,t) v‖²
```

uniformly in the approximating scale and propagate them toward finite OS decay and continuum Hamiltonian lower bounds.

What has changed is the roadmap priority: the current exact-gap lane has isolated a smaller, mode-specific one-slab scalar identity that should be attacked directly from the Wilson kernel before adding another abstract gap certificate.

---

## 9. Finite Dobrushin covariance lane: proved but not the mass-gap mechanism

The repository retains a correct high-temperature finite-volume covariance theorem based on the active single-link majorant

```text
q(β) = (exp(4β)-1)/(exp(4β)+1)
```

and a geometric factor based on `18 q(β)`.

The canonical high-β diagnostic proves

```text
q(β) -> 1
18 q(β) -> 18
```

as `β -> +∞`.

Therefore that particular Dobrushin mechanism cannot supply a scale-independent `< 1` contraction in a scaling regime with `β_n -> +∞`. It remains a valid finite high-temperature theorem and a useful diagnostic, not the current physical continuum mass-gap route.

---

## 10. Full four-dimensional Yang--Mills existence remains open

The same-root scalar continuum process and the finite transfer/Wightman machinery are substantial, but a Clay-level theorem requires a sufficiently rich four-dimensional continuum Yang--Mills theory on one coherent physical carrier.

The remaining construction must ultimately support the required combination of

```text
Euclidean covariance
gauge-invariant local observable content / gauge structure
reflection positivity
regularity / distributional control
physical nontriviality
vacuum structure and clustering
OS/Wightman reconstruction on the same model
and a strictly positive spectral gap above the vacuum
```

with every decisive bridge derived from the finite Wilson root or its proved continuum limit.

Until that is complete, the repository should be described as a formalized constructive program with major theorem chains and sharply localized open seams, not as a completed Millennium-prize proof.

---

## 11. Exact-value claim discipline

The repository contains an internal symbolic exact-gap lane and separate numerical/exact-value material. These must not be conflated without an explicit theorem.

In particular, the current SU(2) common-carrier theorem deliberately exposes

```text
exactGapValueReal
```

without inserting a downstream theorem that identifies it with a numerical literal merely for presentation convenience.

Likewise, the existence of one Hamiltonian eigenmode at a positive energy is not by itself the statement that no spectrum lies below it. “Exact mode”, “spectral floor”, “global mass gap”, and “full Yang--Mills mass gap” remain separate claims unless the corresponding bridges are present in Lean.

---

## 12. Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/

  # current SU(2) completed-boundary / one-slab seam
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabIntertwining.lean
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabMatrixCoefficient.lean
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferPhysicalModeMatrixCoefficient.lean

  # boundary / pair coordinates and physical mode realization
  PhysicalYangMillsGaugeInvariantOSBoundaryTransferSpatialSlicePair.lean
  PhysicalYangMillsGaugeInvariantOSBoundaryExcitationObservableImage.lean
  PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalTransfer.lean

  # finite temporal dynamics
  PeriodicHypercubicSpecialUnitaryDiscretePhysicalTemporalAction.lean
  PhysicalYangMillsOrientedDiscreteTemporalActionCore.lean
  PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation.lean

  # finite/common-carrier and exact-gap transport
  PhysicalYangMillsGaugeInvariantOSApproximatingVacuumOrthogonalSemigroup.lean
  PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer.lean
  PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean

  # transfer spectral / logarithmic-generator / Wightman lane
  # (see ROADMAP.md for the ordered milestone chain)
```

---

## Validation and repository discipline

The authoritative workflow is conservative by design:

```text
proof work starts from the exact canonical SHA
validation proof PRs begin as Draft
CI is accepted only after workflow / job / exact Lean step are terminal success
failed exact heads are repaired only after the failure is terminal and inspected
changes remain additive / tighten-only unless an explicit correction is required
sorry / admit / axiom / placeholder constant escapes are forbidden
replacement PRs receive independent exact-head CI
fresh base/head/mergeability/review/thread checks precede merge
normal merge uses the expected proof-head SHA
GitHub's returned merge SHA is authoritative
post-merge canonical parents and exact HEAD are rechecked
```

The current fast audit policy reports zero occurrences of the forbidden proof tokens across the Lean tree at validated proof heads.

## What to read next

See [`ROADMAP.md`](ROADMAP.md) for the ordered development plan, current completed phases, the exact PR #3151 frontier, and the distinction between the exact-mode route, the global coercive route, and the still-open full 4D Yang--Mills construction.
