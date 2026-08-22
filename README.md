# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills existence and the mass-gap problem.

The repository is intentionally strict about claim boundaries. It separates:

1. **same-root theorems** derived from the actual finite periodic Wilson model and transported through explicit continuum / Osterwalder--Schrader constructions;
2. **generic analytic infrastructure** that proves implications once clearly stated model-facing estimates are supplied; and
3. **open physical-model obligations** that still have to be derived before a Clay-level Yang--Mills existence-and-mass-gap theorem can be claimed.

> **Current claim:** the repository does **not** contain a completed proof of the Clay Millennium Yang--Mills mass-gap problem.
>
> The canonical development now contains a substantial same-root finite-Wilson -> scalar-continuum -> OS/Hamiltonian construction and a large amount of gap-transfer machinery. The decisive remaining quantitative input is a **scale-uniform spectral/Poincaré estimate for the actual finite Wilson shared-boundary transfer operator**. That estimate is not yet derived from the final model.

## Repository status — 2026-08-22 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing checkpoint represented here:
  PR #2006
  formal: record high-beta Dobrushin no-go

Theorem checkpoint merge SHA:
  d1d0d098771c55b906ea689e6af0b55d5b1f5aa4

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative proof status.

---

## Proof picture in one view

```text
ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> finite reflection positivity / OS Gram geometry
  -> primary reflection-fixed rational-time readout
  -> canonical plaquette normalized-trace scalar process
  -> same-root Prokhorov continuum law on ℚ -> ℝ
  -> continuum rational-cylinder OS positivity
  -> fixed-slot OS Hilbert spaces
  -> directed-limit Hilbert carrier
  -> rational contraction semigroup
  -> real strongly continuous contraction semigroup
  -> dense generator / graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ excitation sector

FINITE SPATIAL COVARIANCE LANE

actual finite Wilson Gibbs covariance
  -> two-sided support-localized comparison
  -> finite-support variation bridge
  -> separated-support geometric covariance bound
  -> actual midpoint Wilson-source bounded-continuous carriers
  -> factorial physical-separation decay under a uniform Dobrushin ratio
  -> weak-limit transfer to the same-root scalar continuum covariance
  -> conditional continuum ultralocality

ROUTE DIAGNOSTIC

q(β) = (exp(4β)-1)/(exp(4β)+1)
  -> q(β) -> 1 as β -> +∞
  -> 18 q(β) -> 18
  -> current high-temperature Dobrushin threshold cannot survive β_n -> +∞

PHYSICAL GAP-TRANSFER LANE

finite Wilson OS shared-boundary transfer K_(n,t)
  -> scale-uniform L² Poincaré / exponential-defect estimate       [OPEN CORE]
  -> finite vacuum-orthogonal OS norm decay                         [machinery integrated]
  -> common-carrier finite-to-continuum transfer                     [interface integrated]
  -> continuum Hamiltonian Rayleigh lower bound                     [machinery integrated]
  -> vacuum-sector spectral gap consequences                        [machinery integrated]
```

The immediate frontier is therefore **not** another refinement of the current Dobrushin covariance kernel. The current Dobrushin estimate has now been formally diagnosed as a small-coupling / high-temperature mechanism. The mass-gap route must instead obtain a genuinely model-derived quantitative estimate for the finite Wilson transfer/Hamiltonian structure that is compatible with the intended continuum scaling.

---

## 1. Actual finite compact `SU(N)` Wilson root

The finite model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an actual periodic-even Wilson Gibbs law.

Integrated finite-model infrastructure includes:

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and boundary decomposition
finite Wilson reflection positivity / Gram-square identities
gauge covariance of plaquette holonomy
gauge invariance of normalized real trace-power observables
integer temporal covariance and reflection covariance
finite support / plaquette-local support geometry
```

The interacting boundary law is kept as the actual Wilson marginal; it is not replaced by Haar measure at nonzero coupling.

---

## 2. Same-root scalar continuum OS construction

The canonical continuum carrier currently used for the constructive OS reconstruction is

```text
ℚ -> ℝ
```

for the selected primary plaquette normalized-trace process. It is a genuine same-root continuum observable law obtained as a weak limit of actual finite Wilson pushforwards, but it is **not** yet the full four-dimensional continuum gauge connection.

The integrated route contains:

```text
primary positive-half locality
reflection-completed finite rational path
canonical scalar plaquette readout
tightness / Prokhorov subsequence
continuum rational-cylinder reflection positivity
continuum reflection invariance
positive-semidefinite OS bilinear forms
OS null quotient and fixed-slot Hilbert completion
directed-system and completed direct-limit Hilbert carrier
```

No continuum reflection-positivity axiom is inserted at the end of the construction; the positivity is transported from the finite Wilson model.

---

## 3. Same-root real OS semigroup and Hamiltonian

The canonical primary-scalar OS reconstruction now contains a genuine real strongly continuous contraction semigroup on the zero-time regular sector.

The integrated chain includes:

```text
rational-time contraction
exact rational semigroup laws
canonical zero-time regular sector
NNRat -> NNReal orbit extension
real C₀ contraction semigroup
dense right-generator domain
H_OS = -A_OS
graph closure as a Mathlib LinearPMap
positive-shift resolvents
self-adjoint graph-closed Hamiltonian
Yosida approximation and semigroup recovery
exact generator / closed-Hamiltonian identification
```

The vacuum is constructed from the literal constant-one cylinder and is normalized:

```text
‖Ω‖ = 1
T_t Ω = Ω
H Ω = 0
```

The vacuum-orthogonal excitation carrier

```text
Ω⊥ = {x | inner ℝ Ω x = 0}
```

is complete and invariant under the semigroup, and the exact closed Hamiltonian restriction to the excitation sector is available.

This is substantial OS/Hamiltonian infrastructure, but **a positive excitation lower bound has not been derived from the actual Wilson model merely by constructing this carrier**.

---

## 4. Finite separated-support covariance: what is now proved

The recent development closed a genuine finite-volume static clustering statement for local Wilson observables.

For finite supports separated by plaquette-local distance `D`, the current route gives a bound of the form

```text
|Cov(F,O)|
  <= ((18 q(β))^D / (1 - 18 q(β)))
     * variation_mass(F)
     * variation_mass(O)
```

under the explicit finite high-temperature condition

```text
18 * q(β) < 1,
q(β) = (exp(4β)-1)/(exp(4β)+1).
```

The support interface has been tightened so that bounded-continuous observables depending on finite edge sets automatically receive finite variation profiles. The actual midpoint Wilson-source observables have also been connected to this finite-support covariance route.

This is a real finite Wilson theorem, not an abstract clustering assumption.

---

## 5. Weak-limit covariance transfer and its precise meaning

The finite midpoint Wilson-source covariance has now been rewritten on the fixed scalar path carrier by bounded-continuous left, right, and product tests. Weak convergence therefore transfers the finite covariance to the same-root Prokhorov continuum law.

Combined with a **hypothetical scale-independent** Dobrushin ratio

```text
18 * q(beta n) <= rhoBar < 1
```

and the fact that fixed positive physical separation corresponds to an increasing number of lattice steps, the finite geometric bound forces the limiting midpoint covariance to vanish exactly.

That conclusion is deliberately described as **conditional ultralocality**, not as the desired physical exponential clustering theorem. A scale-independent high-temperature contraction is much stronger than an ordinary finite physical correlation length when the lattice spacing tends to zero.

---

## 6. High-β Dobrushin no-go

PR #2006 formalizes the asymptotic behavior of the current active single-link TV majorant:

```text
q(β) = (exp(4β)-1)/(exp(4β)+1)
q(β) -> 1                 as β -> +∞
18 * q(β) -> 18           as β -> +∞
```

Hence, for any sequence `beta n -> +∞`, neither

```text
18 * q(beta n) < 1
```

nor a uniform bound

```text
18 * q(beta n) <= rhoBar < 1
```

can hold eventually.

This does **not** assert that every continuum coupling sequence in the repository tends to `+∞`; the generic weak-limit construction still accepts an arbitrary nonnegative `beta : ℕ -> ℝ`. It says precisely that **if** the intended physical scaling has `beta n -> +∞`, the current Dobrushin comparison cannot supply the continuum mass-gap mechanism.

---

## 7. Current substantive frontier: shared-boundary `L²` Poincaré gap

The physical OS/Hamiltonian transfer infrastructure has already reduced a positive continuum excitation bound to a concrete finite Wilson estimate.

The cleanest current package is the exponential shared-boundary Poincaré form. For a positive mass parameter `m`, the required scale-uniform estimate is

```text
(1 - exp(-m t)) * ‖v‖²
  <= ‖v‖² - ‖K_(n,t) v‖²
```

for the actual finite Wilson shared-boundary transfer operator `K_(n,t)`, uniformly in the approximating scale `n`.

Once such a model-derived estimate is supplied together with the exact boundary-moment intertwining, the existing mathlib route produces:

```text
boundary L² quadratic contraction
  -> finite Wilson OS vacuum-orthogonal norm decay
  -> positive common small-time slope
  -> finite-to-continuum common-carrier transfer
  -> continuum closed-Hamiltonian Rayleigh lower bound on Ω⊥
  -> vacuum uniqueness / sub-mass spectral exclusion consequences
```

The **open mathematical problem inside the formal development is to derive this finite Wilson boundary estimate from the actual model**, not to insert it as a certificate field.

---

## 8. Full four-dimensional Yang--Mills construction remains open

The same-root scalar rational-time process supports a genuine OS/Hilbert/Hamiltonian reconstruction. It nevertheless captures one selected gauge-invariant scalar observable, not a complete four-dimensional interacting gauge field.

A Clay-level existence theorem still requires a sufficiently rich continuum Yang--Mills construction carrying the necessary model-derived combination of

```text
Euclidean covariance
gauge structure / local gauge-invariant observable content
reflection positivity
regularity / distributional control
clustering / vacuum structure
finite-Wilson compatibility
physical nontriviality
and a positive Hamiltonian mass gap
```

on one coherent physical carrier.

---

## 9. Exact-value and glueball claims remain separate

The repository contains several logically separate numerical or spectral routes. They must not be identified without explicit theorem-level bridges.

In particular:

```text
33/20
  belongs to a separate normalized exact-value / spectral-atom route.

finite Dobrushin constants
  belong to the static high-temperature covariance route.

future m > 0
  must be derived as a genuine positive excitation lower bound for the
  same physical Yang--Mills Hamiltonian carrier.
```

Likewise, finite signed-spatial symmetry and cubic geometry do not by themselves prove a glueball state or glueball mass.

---

## 10. Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/

  # finite Wilson covariance / support localization
  ContinuousCompactOrientedGaugeWilsonFiniteSupportVariation.lean
  PeriodicHypercubicEvenFiniteSupportGibbsCovarianceSpatialGeometric.lean
  PeriodicHypercubicSpecialUnitarySingleLinkTVInfluence.lean
  PeriodicHypercubicSpecialUnitaryActiveTVMajorantHighBeta.lean

  # midpoint covariance -> scalar weak limit
  PeriodicHypercubicEvenMidpointWilsonSourceCovarianceWeakLimitTransfer.lean

  # same-root OS / Hamiltonian construction
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSector.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularClosedHamiltonian.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonal.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumNormalizedCentered.lean

  # finite-to-continuum physical gap transfer
  PhysicalYangMillsGaugeInvariantOSApproximatingVacuumOrthogonalSemigroup.lean
  PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer.lean
  PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareGap.lean
  PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryL2PoincareGap.lean
  PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean
```

---

## Validation and repository discipline

The authoritative workflow is conservative by design:

```text
ordinary proof PRs start from the exact canonical SHA and begin as Draft
GitHub connector is the canonical repository-operation path
CI is judged only after workflow / job / exact Lean step are completed
queued or in_progress heads are never modified
completed failures are repaired only after the exact head is rechecked
changes are additive / tighten-only
sorry / admit / axiom / placeholder constants are forbidden
Ready -> merge requires fresh head/base/mergeability/review/thread checks
green PRs use normal merge with expected head pinned
the GitHub-returned merge SHA is authoritative
post-merge canonical must compare identical / ahead 0 / behind 0
```

## What to read next

See [`ROADMAP.md`](ROADMAP.md) for the ordered proof-development plan and the exact distinction between integrated infrastructure, conditional routes, and the current model-facing frontier.
