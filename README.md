# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Osterwalder--Schrader reconstruction, transfer operators, and the mass-gap problem.

The repository keeps a strict distinction between

1. theorems derived from the actual finite periodic Wilson model;
2. same-root continuum / OS / Hamiltonian constructions built from those finite objects;
3. generic analytic and spectral implication machinery; and
4. model-facing compatibility statements that are still open.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The authoritative branch contains a large formalized theorem chain: finite compact-`SU(N)` Wilson geometry and reflection positivity, same-root scalar continuum OS reconstruction, a graph-closed self-adjoint Hamiltonian framework, completed finite transfer spectral and logarithmic-generator machinery, transfer/Wightman common-core implication machinery, and a sharply reduced `SU(2)` exact-mode realization lane.
>
> The current model-facing seam is no longer the broad selected-mode matrix-coefficient statement described in the previous public README. It has been pushed upstream to an **actual realizable one-lattice-step Wilson synthesis / raw positive-half path-kernel problem**. The remaining finite calculation is now centered on Haar/Fubini/Markov decomposition of the literal normalized `H+1`-slab Wilson path Gram expression into the adjacent temporal-gauge one-slab coefficient.
>
> A selected exact Hamiltonian mode, even when fully realized, is not by itself a proof of a global spectral gap; and the current same-root scalar continuum process is not yet the full four-dimensional continuum Yang--Mills field.

## Repository status — 2026-09-03 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical exact SHA at this documentation checkpoint:
  cfa8a7b31f1904699371882270fde21885a99079

Latest merged mathematical checkpoint represented here:
  PR #3197
  Expose realizable one-step synthesis in raw Wilson path Gram form

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results on `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative proof status. The `main` branch is the public landing surface.

---

## Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> boundary and spatial-slice Haar-L² carriers
  -> normalized physical one-slab transfer
  -> completed pair-Hilbert transfer
  -> positivity / compact spectral support
  -> logarithmic transfer generator / resolvent / spectral-floor machinery

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson primary scalar readout
  -> rational-time path law
  -> same-root Prokhorov continuum law
  -> continuum reflection positivity
  -> OS Hilbert reconstruction
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. TRANSFER / WIGHTMAN SPECTRAL LANE

positive compact physical transfer
  -> strictly-positive spectral support
  -> partial logarithmic generator
  -> spectral-mode operator core
  -> common-core / self-adjoint intertwining machinery
  -> transfer point energies <-> Wightman H|Ω⊥ point energies
  -> spectral-floor / attained-gap implication machinery

D. SU(2) EXACT-MODE LANE

selected physical one-slab mode f_n
  + normalized one-slab top mode ω_n
  -> boundary / pair realization
  -> completed finite OS transfer
  -> common-carrier continuum time-one mode
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal

E. CURRENT RAW FINITE-MODEL SEAM

actual realizable one-lattice-step carrier translation
  -> open-half Haar-L² representative                         [Integrated]
  -> actual boundary synthesis pair coefficient               [Integrated]
  -> rectangular Wilson Gram Hilbert-Schmidt pairing          [Integrated]
  -> raw normalized unfixed H+1-slab path Gram representative [Integrated]
  -> Gauss endpoint temporal-link Haar reduction              [Integrated]
  -> temporal-gauge path Markov/Fubini decomposition
       to adjacent one-slab Wilson coefficient                [OPEN NOW]
  -> RealizableOneStepPhysicalTopRawKernelLimitAtFor          [OPEN NOW]
  -> selected completed-boundary weak identity                [already generated]
  -> downstream exact-mode chain                              [already generated]

F. FULL CLAY-LEVEL COMPLETION

selected exact mode -> global spectral lower bound             [OPEN]
scalar continuum process -> sufficiently rich 4D YM field      [OPEN]
full model-derived OS/Wightman physical carrier                [OPEN]
strictly positive spectrum above the vacuum                    [OPEN]
Clay-level existence + mass gap                                [OPEN]
```

---

## 1. Actual finite compact `SU(N)` Wilson root

The finite model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical finite-model infrastructure includes

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
boundary and spatial-slice Haar-L² carriers
normalized one-slab physical transfer
completed excitation-pair transfer
compactness / self-adjointness / positivity
```

The interacting Wilson law is not silently replaced by an unrelated abstract measure at the decisive model-facing steps.

---

## 2. Same-root scalar continuum OS construction

The constructive continuum lane currently uses a selected primary gauge-invariant scalar Wilson process, schematically

```text
ℚ -> ℝ.
```

It is obtained from finite Wilson pushforwards and therefore remains connected to the finite root. The integrated route includes

```text
primary positive-half locality
reflection-completed rational-time paths
tightness / Prokhorov subsequence
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completions
directed-system / direct-limit Hilbert carrier
```

This is a genuine same-root continuum observable law. It is **not** yet the full continuum gauge connection or the complete local observable net on `ℝ⁴`.

---

## 3. Real OS semigroup, Hamiltonian, vacuum, and `Ω⊥`

The canonical OS lane contains a real strongly continuous contraction semigroup and a graph-closed self-adjoint Hamiltonian framework.

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
vacuum Ω with ‖Ω‖ = 1, T_t Ω = Ω, H Ω = 0
complete vacuum-orthogonal carrier Ω⊥
```

A Hamiltonian carrier is an essential structural step, not by itself a mass-gap theorem.

---

## 4. Completed transfer, logarithmic generator, and spectral floor machinery

The finite transfer lane has been developed well beyond a single norm estimate. Canonical results include

```text
completed pair-transfer construction
self-adjoint contraction structure
positivity from finite tensor / Schur-product arguments
compact positive spectral support
transfer/generator spectral relations
below-gap and above-one resolvent calculus
all-order scalar resolvent derivative hierarchies
strictly-positive support logarithmic generator
spectral-mode eigenvector/domain theorems
intrinsic logarithmic spectral floor
resolvent-moment / effective-energy variational identifications
```

The logarithmic generator remains partially defined where the mathematics requires it; it is not replaced by an artificial everywhere-defined surrogate.

---

## 5. Transfer-to-Wightman bridge machinery

The transfer/Wightman architecture has been tightened from global assumptions to common-core data.

Integrated reductions include

```text
two dense isometric core realizations -> canonical Hilbert equivalence
closed-subspace corestriction
Mathlib LinearPMap.HasCore closure transfer
self-adjoint maximality
positive-transfer spectral span as source operator core
mode-wise source/target action -> common-core action
common-core action -> full intertwining
point-energy-set transport
spectral-floor / Wightman gap-certificate implications
```

This machinery precisely identifies what local model equations would be sufficient. It does not pretend that every required Wightman realization identity has already been derived from the finite Wilson root.

---

## 6. The `SU(2)` exact-mode lane

A separate `SU(2)` lane carries the symbolic exact-mode quantity

```text
exactGapClusterContractionRatio = exp (-exactGapValueReal).
```

Once its finite realization hypotheses are supplied, the existing downstream chain produces a continuum OS time-one eigenmode and a graph-closed vacuum-orthogonal Hamiltonian mode with energy

```text
exactGapValueReal.
```

The dependency direction has been repeatedly tightened so that the downstream eigen-equation is not reused to prove its own finite input.

Important claim discipline:

```text
one positive Hamiltonian eigenmode != global spectral gap
exactGapValueReal != a numerical literal unless Lean proves that equality
selected scalar continuum process != full 4D Yang--Mills field
```

---

## 7. What changed after the previous public checkpoint

The previous README stopped at PR #3151, where the model-facing exact-mode seam had been reduced to selected pair-Haar matrix coefficients. The canonical branch has since moved substantially upstream.

### PR #3157 — raw one-slab coefficient

The selected one-step right-hand side was rewritten as the literal normalized temporal-gauge one-slab Wilson Hilbert-Schmidt kernel coefficient. Arbitrary pair-Haar tests are retained; no decomposable-test density shortcut is used.

### PR #3162 — remove completion opacity

Every completed boundary-transfer coefficient is approached by coefficients of actual Wilson synthesis outputs from dense raw OS carriers.

### PR #3166 — expose finite/common one-step coherence

The repository now isolates the exact scale-local predicate

```lean
R.CommonSemigroupOneStepCoherentAt hInvariant C n
```

meaning the common `C.translate 1` agrees with the actual realizable finite one-lattice-step translation at cutoff `n`. The equality is explicit rather than hidden in definitional simplification.

### PR #3171 — projected synthesis density for arbitrary ambient inputs

The density argument was extended through the canonical projected completed-boundary range without assuming surjectivity of the boundary embedding.

### PR #3177 — push the old weak seam to a raw-kernel limit

The former completed weak hypothesis is theorem-generated from

```lean
RealizableOneStepPhysicalTopRawKernelLimitAtFor
```

plus the explicit one-step coherence predicate. This new seam contains no continuum eigen-equation or Hamiltonian input.

### PRs #3181 and #3185 — literal realizable lattice step

The canonical positive-half pullback under realizable integer lattice time was computed pointwise and then lifted to the actual open-half Haar-`L²` representative. The one-step input can therefore be read as the original positive-half pullback evaluated on the literal temporal section step.

### PR #3191 — actual synthesis coefficient = Wilson Gram pairing

Every pair-Haar matrix coefficient of actual one-step adjoint synthesis was identified with the canonical rectangular Hilbert-Schmidt Wilson Gram-kernel pairing.

### PR #3197 — raw `H+1`-slab path Gram representative

The rectangular completed positive-boundary Gram `L²` kernel now has, almost everywhere, the literal partition-normalized unfixed Wilson positive-half path kernel as representative. The pair-coordinate Gram identity

```text
<A† A z, z> = ‖A z‖²
```

is also exposed without introducing a duplicate Gram construction.

This matters because the remaining seam is now an explicit finite path-integral calculation rather than an opaque completed-Hilbert compatibility assumption.

---

## 8. A key finite Haar/gauge-reduction theorem is already present

The repository already contains the exact Gauss-law endpoint identity

```lean
periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_temporalGauge
```

in

```text
PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction.lean
```

It proves that after integrating the temporal-link field against normalized product Haar, an unfixed positive-half endpoint amplitude with a gauge-invariant terminal state equals the corresponding temporal-gauge spatial-path amplitude.

Therefore the next frontier should **not** be described as “first prove temporal-link Haar gauge fixing.” That part is already formalized.

---

## 9. Immediate frontier after PR #3197

The remaining selected-mode finite theorem is the bridge

```text
raw normalized H+1-slab boundary/open-half Gram coefficient
  + literal realizable one-step input
    -> endpoint-amplitude / product-Haar form
    -> existing Gauss endpoint iterated-Haar reduction
    -> temporal-gauge spatial-path amplitude
    -> finite Markov/Fubini decomposition
    -> adjacent temporal-gauge one-slab Wilson coefficient
```

The target model predicate is

```lean
RealizableOneStepPhysicalTopRawKernelLimitAtFor
```

from

```text
PhysicalYangMillsWilsonSU2CompletedBoundaryTransferRealizableOneStepRawKernelLimit.lean
```

Once that predicate is proved for the selected `SU(2)` mode family, existing canonical theorems already convert it, together with explicit `CommonSemigroupOneStepCoherentAt`, into

```text
selected completed-boundary raw-kernel weak identity
  -> selected pair weak intertwining
  -> finite/common exact-mode chain
  -> continuum OS time-one eigenmode
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal.
```

No downstream eigen-equation should be assumed in order to prove this finite path-integral identity.

---

## 10. Finite/common-time coherence remains explicit

Two dynamics remain logically distinct:

```text
C.translate 1
```

for the common `NNReal` semigroup family, and

```text
R.positiveTranslation n 1
```

for the actual cutoff one-lattice-step Wilson dynamics.

PR #3166 made the required equality explicit as `CommonSemigroupOneStepCoherentAt`. Later PRs compute the actual lattice action cleanly, but the common-family equality is still a model-facing coherence statement and must not be silently assumed.

---

## 11. Global gap and full four-dimensional Yang--Mills remain downstream

The exact-mode lane and the global lower-bound lane are different tasks.

The scale-uniform Poincaré/coercive machinery remains relevant for proving a **global vacuum-orthogonal spectral lower bound**, schematically through estimates such as

```text
(1 - exp(-m t)) * ‖v‖²
  <= ‖v‖² - ‖K_(n,t) v‖²
```

uniformly in the approximating scale.

Separately, a Clay-level theorem requires a sufficiently rich same-root continuum four-dimensional Yang--Mills theory with the required combination of

```text
Euclidean covariance
gauge-invariant local observable content / gauge structure
reflection positivity
regularity / distributional control
physical nontriviality
vacuum structure and clustering
OS/Wightman reconstruction on the same model
a strictly positive spectral gap above the vacuum
```

The repository should therefore be read as a formalized constructive program with major theorem chains and sharply localized open seams, not as a completed Millennium-prize proof.

---

## 12. Dobrushin lane: valid diagnostic, not the active continuum mechanism

The finite high-temperature covariance lane remains correct, with a single-link majorant

```text
q(β) = (exp(4β)-1)/(exp(4β)+1)
```

and a geometric factor based on `18 q(β)`. Since `q(β) -> 1` and `18 q(β) -> 18` as `β -> +∞`, this particular Dobrushin mechanism cannot provide a scale-independent `< 1` contraction in the large-`β` scaling regime. It remains a useful finite-volume theorem and obstruction diagnostic.

---

## 13. Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/

  # raw realizable one-step / exact-mode seam
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferRealizableOneStepRawKernelLimit.lean
  PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisPairKernel.lean
  PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram.lean

  # positive-half path coordinates and Haar / temporal-gauge reduction
  PeriodicHypercubicEvenBoundaryPositiveHalfClosureTransferKernelBridge.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCylinderActionIdentification.lean

  # actual one-slab kernel / transfer factorization
  PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferPositive.lean
  PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferFactorization.lean

  # common / realizable one-step coherence
  PhysicalYangMillsGaugeInvariantOSCommonRealizableOneStepCoherence.lean
  PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfTemporalStep.lean
  PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfL2TemporalStep.lean

  # completed-boundary synthesis density
  PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferSynthesisDensity.lean
  PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferProjectedSynthesisDensity.lean

  # downstream exact-gap / Hamiltonian transport
  PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer.lean
  PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean
```

File names are listed to make the current proof boundary auditable from the code rather than only from prose.

---

## Validation and repository discipline

The theorem workflow is intentionally conservative:

```text
start proof work from the exact authoritative canonical SHA
validate theorem units on Draft PRs
accept CI only when workflow / job / exact Lean step are terminal success
never count queued or in_progress as a proof receipt
repair failed heads only after terminal failure and log inspection
forbid sorry / admit / axiom / placeholder-constant escapes
close successful validation Drafts unmerged
create independent non-Draft replacements from the fresh canonical base
require independent exact-head CI on replacements
fresh-check head/base/mergeability/reviews/threads before merge
normal merge with expected proof-head SHA pinned
verify post-merge canonical HEAD and both merge parents
```

The current validated proof heads report zero forbidden proof tokens across the audited Lean tree.

## What to read next

See [`ROADMAP.md`](ROADMAP.md) for the ordered proof-development plan, the PR #3157--#3197 reduction chain, the exact finite Haar/Markov/Fubini frontier, the separate common-time coherence obligation, and the still-open global spectral-gap / full four-dimensional Yang--Mills program.
