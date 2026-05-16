# MGAP4D

MGAP4D is a Lean 4 repository for developing, checking, and auditing the proof architecture of a normalized 4D mass gap theorem.

The repository is GitHub-native: Lean source, CI, audit scripts, replay guides, theorem-surface maps, bridge audits, target-obligation layers, and public-boundary ledgers live directly in this repository.

## Repository role

This repository is the canonical Lean proof repository for the MGAP4D normalized 4D mass gap proof architecture.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final public theorem release.

## Current theorem claim and boundary

Inside the MGAP4D Lean proof architecture, the current theorem-body surface records the normalized exact spectral gap value:

```text
exactGapValueReal = 33 / 20
```

The repository treats `33/20` as an internal normalized theorem-body value, not as a packaging artifact, CI artifact, manifest-only artifact, or prototype-only release wrapper.

The physical Hamiltonian normalization is read through an explicit reference energy scale `E0`:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

In MGAP4D internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
```

For dimensional interpretation:

```text
physicalGap_dimensional = E0 * (33/20)
```

Thus `33/20` is the dimensionless spectral gap of the normalized physical Hamiltonian. A dimensional physical gap requires an external reference scale `E0`.

The repository currently claims an internal normalized proof-architecture theorem-body surface with CI, bridge-audit, and target-obligation support.

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI ledgers replace mathematical proof review
that bridge-coherence audit replaces Lean kernel checking
that the infinite-dimensional target layer alone completes the continuum proof
```

The public final theorem boundary remains review-gated pending independent replay and external audit.

## Active Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

`MGAP4D/MathlibAnalytic.lean` now imports the infinite-dimensional Yang--Mills target-obligation layer:

```text
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
```

## Main analytic chain

```text
Concrete Hilbert realization
  -> Concrete H_phys / unbounded-operator realization
  -> Physical unbounded-operator skeleton
  -> Concrete Yang-Mills Hamiltonian skeleton
  -> Spectral/PVM realization skeleton
  -> Continuum spectral theorem skeleton
  -> Final theorem release skeleton / closure
  -> Concrete residual closure
  -> Physical Hamiltonian normalization bridge
  -> Infinite-dimensional Yang-Mills realization target
  -> Exact value theorem-body origin certificate
```

Key source files:

```text
MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean
MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean
MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseSkeleton.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseClosure.lean
MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean
```

## Evolution beyond the prior weakness

A prior weakness was explicit:

```text
many Lean files closed proof structure, bridge boundaries, and audit surfaces,
but did not yet provide a full analytic infinite-dimensional Yang-Mills Hamiltonian realization.
```

The current evolution does not hide that weakness. It turns it into a first-class Lean target layer:

```text
InfiniteDimensionalYangMillsRealizationTarget
InfiniteDimensionalYangMillsRealizationTarget.ready
InfiniteDimensionalYangMillsTargetReviewSurface
infinite_dimensional_yang_mills_target_review_surface_ready
```

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

This is a typed analytic proof-obligation surface. It is not a completed public final continuum proof.

## CI and audit status

### Core local replay

```bash
bash scripts/check.sh
```

The local replay path now runs:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] replay summary
[check] lake update
[check] lake build
```

### Audit scripts

```text
scripts/verify_manifest.py
scripts/audit_lean_forbidden_tokens.py
scripts/audit_major_theorem_nonplaceholder.py
scripts/audit_bridge_coherence.py
scripts/audit_infinite_dimensional_target_layer.py
scripts/replay_summary.py
scripts/check.sh
```

### GitHub Actions workflows

```text
.github/workflows/lean-direct-elan.yml
.github/workflows/bridge-coherence-ci.yml
.github/workflows/full-local-check.yml
```

`Full Local Check CI` mirrors the external-review one-command replay by running:

```bash
bash scripts/check.sh
```

A confirmed Full Local Check CI run has already succeeded:

```text
Workflow: Full Local Check CI
Run ID: 25948605211
Job ID: 76281846717
Job name: Run scripts/check.sh
Commit checked out by CI: bd3111714d81b6e51615a7b912fec33c0a69d3bc
Result: success
```

That run confirmed:

```text
Lean files scanned: 447
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 7 at that checkpoint
Ordered import edges audited: 4 at that checkpoint
lake build: Build completed successfully
```

After the new target layer, the bridge-coherence audit has been extended to cover 8 bridge / target files and 5 ordered import edges.

## External review entry points

Start here:

```text
EXTERNAL_AUDIT_PACKET.md
```

Then use:

```text
EXTERNAL_REVIEW_CHECKLIST.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/full_local_check_ci.md
```

## Review meaning

A successful replay means:

```text
the repository builds with the pinned Lean toolchain
the declared audit scripts pass
the theorem-surface, bridge-surface, and target-layer checks pass
the replay summary is reproducible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
CI output alone is a substitute for proof review
the target layer alone completes the physical continuum proof
```

## Build

```bash
lake update
lake build
```

or full local replay:

```bash
bash scripts/check.sh
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native documentation and checkpoint ledger
maps/                    Lightweight source and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Citation and Zenodo record

A DOI-backed technical report for the Phase 3 spectral gap formalization checkpoint is archived on Zenodo:

```text
Hidetoshi Itakura, A Lean 4 Proof Architecture for a Normalized 4D Mass Gap Theorem: Phase 3 Spectral Gap Formalization and External-Audit Boundary, Zenodo, 2026. DOI: 10.5281/zenodo.20181046.
```

```text
Zenodo record: 20181046
DOI: 10.5281/zenodo.20181046
URL: https://zenodo.org/records/20181046
Repository citation metadata: CITATION.cff
Repository receipt: docs/zenodo_record_20181046.md
```

This Zenodo record is a proof-architecture and external-audit preparation report. It does not by itself open public final theorem release.
