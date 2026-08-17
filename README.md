# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository keeps three logically different layers separate:

1. theorem infrastructure and model-specific results already merged into the authoritative carrier;
2. conditional theorem routes whose assumptions remain explicit in Lean; and
3. model-facing continuum construction obligations that are still open.

The repository does **not** currently claim an unconditional construction of interacting four-dimensional continuum Yang--Mills theory, and it does **not** claim a completed proof of the Clay Millennium problem.

## Repository status — 2026-08-18 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing checkpoint:
  PR #1767
  Lift continuum rational finite reflection laws to full path invariance

Theorem checkpoint merge SHA:
  b4196326db0b6d5d5e96bb55046a641aaffef9ea

Checkpoint validation:
  PR Lean Fast Check #10809
  completed / success

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md
```

Documentation-only merges may advance the carrier branch tip beyond the theorem checkpoint SHA without changing the theorem state described here. Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status.

## Current proof picture

The project now has two highly developed theorem lanes that still have to be joined by an **actual same-root continuum OS-positive Yang--Mills construction**.

### A. Actual Wilson -> same-root rational continuum path law

```text
actual periodic-even compact SU(N) Wilson Gibbs model
  -> finite Wilson reflection positivity / OS geometry
  -> gauge-invariant plaquette and normalized-trace observables
  -> boundary-vacuum scalar readout on the actual Gibbs source
  -> exact integer temporal covariance and reflection covariance
  -> factorial rational-time floor embedding
  -> path-valued Prokhorov subsequence limit on ℚ -> ℝ
  -> finite rational-cylinder reflection law                    [#1765]
  -> continuum finite rational-cylinder reflection law          [#1766]
  -> full continuum rational-path reflection invariance         [#1767]
  -> same-root rational positive-time OS reflection positivity  [OPEN NOW]
```

The carrier `ℚ -> ℝ` is the countable rational-time skeleton of the constructed boundary-vacuum observable. It is a genuine continuum probability law obtained from the actual Wilson root, but it is **not by itself** a complete continuum gauge connection on `ℝ⁴`.

### B. Physical OS semigroup -> graph-closed Hamiltonian mass

On the already formalized physical OS/Hamiltonian interfaces, the repository proves

```text
physicalYangMillsMass
  = physicalYangMillsOSInfraredMass
  = greatest full-sector uniform exponential semigroup decay rate.
```

In particular, for every vacuum-orthogonal physical vector under the explicit assumptions of that lane,

```text
‖T_t ψ‖ <= ‖ψ‖ * exp (-physicalYangMillsMass * t).
```

The reverse infrared comparison is generated from the semigroup generator, graph-closed Hamiltonian Rayleigh lower bound, right-derivative control, Mathlib's scalar Gronwall theorem, and density/closure of the canonical generator domain. No spectral-attainment premise and no extra functional-calculus identity `T_t = exp(-tH)` is inserted.

This analytic identity is **not yet an unconditional theorem of the bare same-root Wilson continuum law**. The missing bridge is model-derived continuum OS reflection positivity and the corresponding same-root physical reconstruction.

## Major integrated theorem spine

### 1. Continuum OS / Hilbert / Hamiltonian infrastructure

The repository contains reusable formal infrastructure for

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
positive-time contraction semigroups
strong continuity and right-generator domains
graph-closed physical Hamiltonians
self-adjoint / symmetric operator interfaces
PVM and bounded-Borel spectral calculus
scalar spectral measures
vacuum-orthogonal Rayleigh and variational mass interfaces.
```

These theorems transport consequences from supplied OS data. They do not by themselves manufacture the interacting continuum Yang--Mills measure.

### 2. Actual finite compact `SU(N)` Wilson / OS geometry

The finite compact-gauge lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure and contains actual periodic Wilson Gibbs laws, finite reflection-positive Wilson forms, completed finite OS carriers, boundary-Haar/interacting-boundary `L²` realizations, temporal boundary-vacuum observables, and concrete plaquette/cylinder analysis.

The interacting reflection-fixed boundary law is kept as the actual Wilson marginal rather than silently replaced by Haar measure at nonzero coupling.

### 3. Actual Wilson positive-time theorem bridge

PR #1670 integrated the reusable theorem bridge

```text
actual finite Wilson strictness
  -> bounded-continuous actual plaquette/cylinder representatives
  -> canonical C0 -> L2 transport
  -> positive-time submodule / coherent pullback range interfaces
  -> reconstructed nonzero vacuum-orthogonal excitation
  -> Hamiltonian-domain / Rayleigh / physical-mass handoff.
```

The bridge does not assume global surjectivity or multiplicativity of the coherent positive-half pullback, does not insert an abstract dense-carrier premise for the target mode, introduces no duplicate physical Hilbert space, and does not identify static `A†A` with Euclidean time evolution.

### 4. Constructive finite gauge invariance

The actual finite periodic compact-gauge geometry proves gauge covariance of oriented plaquette holonomies and gauge invariance of the normalized real trace-power observables used downstream. The finite observable lane therefore does not require a separate gauge-invariance axiom for these quantities.

### 5. Same-root rational path construction

The rational-time floor path is constructed directly from the same finite Wilson configuration:

```text
q ↦ Ψ_boundary^( floor(q / a_n) )(A).
```

Canonical factorial lattice spacing gives eventual exact lattice alignment for every fixed rational time and every fixed finite rational tuple.

The arithmetic identity

```text
floor(-x) = -floor(x)
```

is **not** assumed in general; the required oddness is used only after exact lattice alignment has been proved.

### 6. Same-root Prokhorov continuum law

The rational path carrier is a countable product Polish space. Tightness/Prokhorov machinery therefore extracts a subsequential continuum probability measure from the actual finite Wilson pushforward laws while preserving the physical scaling subsequence.

The result is an actual same-root continuum law on `ℚ -> ℝ`, not an independently postulated continuum process.

### 7. Finite rational reflection law — PR #1765

Deterministic aligned reflection covariance and exact reflection invariance of the actual finite Wilson Gibbs measure give, for every fixed finite rational tuple, eventual equality of the reflected and unreflected joint laws along the factorial Prokhorov subsequence.

### 8. Continuum finite rational reflection law — PR #1766

Mathlib's continuous mapping theorem passes the finite-cylinder pushforwards through the path-valued weak limit. Eventual exact equality of the finite laws plus Hausdorff uniqueness of the weak limit yields, for every labelled finite rational tuple `time : Fin m -> ℚ`,

```text
map (x ↦ fun i => x (-time i)) L.continuumMeasure
  =
map (x ↦ fun i => x ( time i)) L.continuumMeasure.
```

### 9. Full rational-path reflection invariance — PR #1767

The finite-dimensional theorem is reindexed to arbitrary finite index types and then to every `Finset ℚ`. Mathlib's finite-dimensional-law uniqueness theorem

```lean
ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
```

then closes the full product-measure step:

```text
map θ L.continuumMeasure = L.continuumMeasure,
θ x q = x (-q).
```

This theorem entered the authoritative carrier at `b4196326db0b6d5d5e96bb55046a641aaffef9ea`.

Reflection invariance is a geometric measure-level input. It is **not** the same statement as OS reflection positivity.

### 10. Physical OS infrared mass equals Hamiltonian mass — PR #1763

The state-independent physical OS infrared mass is identified with the graph-closed physical Hamiltonian variational mass:

```text
physicalYangMillsOSInfraredMass = physicalYangMillsMass.
```

### 11. Physical mass is the optimal uniform decay rate — PR #1764

Define a real rate `r` to be a uniform vacuum-orthogonal decay rate when

```text
forall t >= 0, forall ψ ⟂ Ω,
  ‖T_t ψ‖ <= ‖ψ‖ * exp (-r * t).
```

The repository proves that `physicalYangMillsMass` is an attained greatest element of this rate set (`Set.IsGreatest`).

## Immediate frontier: same-root continuum OS reflection positivity

The next substantive model-facing target is no longer full path reflection invariance. That step is integrated. The current target is to construct the **positive-time rational cylinder algebra on the same continuum law** and prove its OS reflection form is nonnegative.

For an appropriate positive-time cylinder observable `F`, schematically:

```text
0 <= ∫ conj(F(θ x)) * F(x) dL.continuumMeasure(x).
```

The exact real/complex formulation should reuse the repository's existing OS conventions.

The finite ingredient is already theorem-generated: the actual finite Wilson model has Gram/reflection positivity. The missing same-root continuum bridge is to:

```text
1. construct positive rational-time cylinder observables;
2. pull them back to actual finite Wilson positive-half observables at aligned scales;
3. identify the finite reflection form with the Wilson Gram/OS form;
4. use factorial eventual alignment;
5. prove convergence of those finite reflection forms along the same Prokhorov subsequence;
6. instantiate the existing automatic reflection-limit positivity machinery;
7. obtain continuum rational-cylinder OS reflection positivity.
```

This route must not replace the actual Wilson source by an unrelated continuum measure or add continuum OS positivity as a new axiom.

## Downstream model-facing obligations

### Same-root OS reconstruction

After continuum rational-cylinder OS positivity is available, instantiate the existing quotient/completion, contraction-semigroup, graph-closed Hamiltonian, and physical-mass infrastructure on that same-root law.

This is the bridge required before the integrated equality

```text
physicalYangMillsMass = physicalYangMillsOSInfraredMass
```

can be advertised as a theorem of the explicitly constructed Wilson continuum object rather than a theorem of supplied physical OS interfaces.

### Full four-dimensional continuum gauge field

The rational boundary-vacuum path is a concrete same-root continuum observable skeleton. A Clay-level construction still requires a sufficiently rich four-dimensional continuum Yang--Mills field/state with the required model-derived Euclidean, gauge, regularity, clustering/vacuum, OS, and finite-Wilson compatibility properties.

### Selected moving-time finite-Wilson recovery

A separate finite-to-continuum dynamical lane remains open. For the theorem-generated finite slow states `phi_n`, the characteristic quantitative obligation is

```text
‖ iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ‖
  <= 2 a_n delta_n,

delta_n -> 0.
```

Equivalently, the residual is `o(a_n)`. Ordinary fixed-time convergence is not a substitute for this moving-time estimate.

The OS infrared/Hamiltonian mass equality does not silently prove convergence of the intrinsic finite Wilson rates.

### Physical exact-value normalization

The normalized `33/20` theorem route remains distinct and conditional. A physical interpretation requires independently derived model component extrema, sharpness, actual identification with `physicalYangMillsMass`, and a physical reference-time/unit normalization.

## Numerical discipline

The following quantities remain distinct unless an explicit theorem connects them:

```text
1/2
  finite high-temperature Z₂ geometric-transfer cap / coercivity constant

physicalYangMillsMass
  graph-closed physical Hamiltonian variational mass
  = physical OS infrared mass
  = optimal full-sector uniform exponential decay rate
  on the integrated physical OS analytic interfaces

33/20
  normalized endpoint of a separate conditional exact-value route
```

The repository does not identify `1/2` or `33/20` with the physical Yang--Mills mass merely because they occur in the broader program.

## Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalReadout.lean
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding.lean
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReflectionAlignment.lean
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFiniteReflectionLaw.lean
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathContinuumFiniteReflectionLaw.lean
  PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathContinuumReflectionInvariance.lean

  FiniteWilsonOSAutomaticReflectionLimitTransfer.lean
  FiniteWilsonGibbsSingleSourceAutomaticOSLimitAssembly.lean

  PhysicalYangMillsGaugeInvariantOSDerivedMassTransfer.lean
  PhysicalYangMillsGaugeInvariantOSContinuumTimeReflection.lean
```

## Validation and repository discipline

The authoritative workflow is intentionally conservative:

```text
ordinary PRs start from the exact authoritative SHA and begin as Draft
GitHub connector is the canonical repository-operation path
CI decisions use completed workflow / job / Lean-step results only
queued or in_progress CI is never treated as final evidence
do not append commits to a PR head while its CI is running
separate Lean/code failures from Actions/cache/external failures
keep development additive / tighten-only
never introduce sorry / admit / axiom / placeholder constants
fix the final head before Ready
re-check exact head, base, mergeability, reviews and threads before integration
green PRs are integrated by normal merge with the expected head pinned
record the new exact authoritative merge SHA
start the next Draft from that exact SHA.
```

The public `main` branch is a landing surface; the authoritative theorem carrier is `formal/real-hilbert-uniform-coercive-strong-limit`.

## Claim boundary

MGAP4D does **not** currently claim:

- an unconditional interacting four-dimensional continuum `SU(N)` Yang--Mills construction;
- a completed Clay Millennium mass-gap proof;
- that the rational boundary-vacuum path law is already the complete continuum gauge field;
- that reflection invariance by itself implies OS reflection positivity;
- that same-root rational-cylinder OS reflection positivity is already proved;
- that the physical OS/Hamiltonian mass identification has already been instantiated from the bare same-root Wilson continuum law;
- that fixed-time convergence proves the selected moving-time `o(a_n)` residual;
- that finite `Z₂` coercivity `1/2` is the physical Yang--Mills mass;
- that `33/20` has already been derived as a physical mass in fixed physical units.

The current development principle is

```text
actual finite Wilson geometry
  -> same-root finite observable laws
  -> same-root continuum path/field laws
  -> model-derived OS positivity and Euclidean structure
  -> OS reconstruction and graph-closed Hamiltonian
  -> physical mass theorem
  -> only then independent numerical normalization.
```

See `ROADMAP.md` for the current milestone order and completion criteria.
