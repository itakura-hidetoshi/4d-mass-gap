# Infinite-dimensional Yang--Mills Target Layer

This document records the evolution from skeleton / contract closure toward explicit analytic proof obligations for a physical continuum Yang--Mills realization.

## Purpose

The previous public weakness was clear:

```text
many Lean files closed proof structure, bridge boundaries, and audit surfaces,
but did not yet provide a full analytic infinite-dimensional Yang--Mills Hamiltonian realization.
```

The new target layer does not hide this weakness. It turns it into a first-class Lean-facing target surface.

## Lean source

```text
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
```

The file is imported by:

```text
MGAP4D/MathlibAnalytic.lean
```

and is audited by:

```text
scripts/audit_bridge_coherence.py
scripts/audit_infinite_dimensional_target_layer.py
```

## Core objects

```text
InfiniteDimensionalYangMillsRealizationTarget
InfiniteDimensionalYangMillsRealizationTarget.ready
InfiniteDimensionalYangMillsTargetReviewSurface
infinite_dimensional_yang_mills_target_review_surface_ready
```

## Target obligations

The target layer requires explicit witnesses for:

```text
infinite-dimensional Hilbert realization
separable Hilbert witness
dense core
domain density
symmetric H_phys
self-adjoint H_phys
gauge-invariant sector
Yang-Mills energy witness
continuum limit
OS positivity
spectral theorem
exact atom
positive plaquette spectral weight
nonempty vacuum-orthogonal sector
normalization preservation
public boundary held
final release held
```

## Theorem surfaces

The layer exposes theorem surfaces that make selected obligations extractable from the readiness predicate:

```text
infinite_dimensional_target_requires_infinite_dimension
infinite_dimensional_target_requires_self_adjoint_hphys
infinite_dimensional_target_requires_continuum_limit
infinite_dimensional_target_requires_plaquette_weight
infinite_dimensional_target_normalized_gap_eq_exact
infinite_dimensional_target_exact_value_eq_3320
infinite_dimensional_target_public_boundary_held
infinite_dimensional_target_final_release_held
```

## Audit integration

The bridge-coherence audit now checks this layer for anchors including:

```text
InfiniteDimensionalYangMillsRealizationTarget
infinite_dimensional_witness
separable_hilbert_witness
dense_core_witness
domain_density_witness
hphys_self_adjoint_witness
gauge_invariance_witness
yang_mills_energy_witness
continuum_limit_witness
spectral_theorem_witness
plaquette_nonzero_weight_witness
vacuum_orthogonal_nonempty_witness
normalized_gap_eq_exact
exact_value_eq_3320
publicBoundaryHeld
finalReleaseHeld
```

The dedicated target-layer audit also checks this file, the root import, and the documentation anchor. This means the target layer is not merely documentation. It is part of the mechanical audit path.

## Confirmed CI run

```text
Workflow: Lean Direct Elan CI
Run ID: 25949068263
Audit job ID: 76283200344
Build job ID: 76283207049
Build job name: Build Lean project via direct elan
Commit checked out by CI: f515f7ceb13bfb1e983196898464fd54101b0afe
Result: success
Date: 2026-05-16
```

Confirmed audit job steps:

```text
Verify release manifest: success
Audit Lean forbidden tokens: success
Audit major theorem non-placeholder surface: success
Audit analytic bridge coherence: success
Audit infinite-dimensional Yang-Mills target layer: success
Summarize Lean replay surface: success
```

Confirmed build job steps:

```text
Confirm direct elan workflow: success
Cache elan and Lake build artifacts: success
Install elan and Lean toolchain: success
Show Lean and Lake versions: success
Generate Lake manifest: success
Pull Mathlib cache when available: success
Build Lean project with lake build: success
```

Confirmed toolchain:

```text
Lean (version 4.30.0-rc2, x86_64-unknown-linux-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
Lake version 5.0.0-src+3dc1a08 (Lean version 4.30.0-rc2)
```

Confirmed audit/build facts:

```text
Lean files scanned: 448
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 8
Ordered import edges audited: 5
Infinite-dimensional target-layer audit: passed
lake build: Build completed successfully
```

## Boundary

This layer is a proof-obligation target, not a completed public final theorem.

It does not claim:

```text
completed infinite-dimensional Hilbert construction
completed self-adjoint Yang-Mills Hamiltonian construction
completed continuum limit proof
completed continuum spectral theorem
completed nonzero plaquette spectral-weight theorem
external mathematical consensus
Clay-style public final theorem acceptance
```

It does claim that these requirements are now explicitly named, imported, audited, and CI-confirmed as the next analytic hardening surface.

## Correct interpretation

Correct:

```text
The repository has evolved from structure-only closure toward a typed analytic target surface that records the exact obligations needed for physical realization.
```

Incorrect:

```text
The target layer by itself completes the physical continuum Yang-Mills proof.
```

## Review use

External reviewers should use this layer to identify the next mathematical proof targets:

```text
1. infinite-dimensional Hilbert construction
2. dense domain / core construction
3. self-adjointness of H_phys
4. gauge-invariant physical sector
5. continuum limit
6. spectral theorem / exact atom
7. nonzero plaquette spectral weight
8. vacuum-orthogonal nonempty sector
9. normalization preservation
```

Each item should eventually be hardened from target witness into concrete theorem body.
