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

The repository currently claims an internal normalized proof-architecture theorem-body surface with CI, bridge-audit, target-obligation, residual-hardening, and external-audit-readiness support.

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI ledgers replace mathematical proof review
that bridge-coherence audit replaces Lean kernel checking
that the external-audit-readiness gate replaces independent replay
```

The public final theorem boundary remains review-gated pending independent replay and external audit.

## Active Lean roots and dependency lane

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

The current Lake project pins Lean/mathlib through:

```text
leanprover/lean4:v4.30.0-rc2
mathlib4 @ v4.30.0-rc2
```

The `MathlibAnalytic` root is a scoped analytic lane. It does not by itself open public final theorem release.

## Main analytic hardening chain

```text
Exact normalized value / real positivity
  -> gap infimum / Rayleigh lower bound / Rayleigh attainment
  -> spectral mass / exact gap analytic closure
  -> Hilbert, H_phys, spectral theorem, PVM, observable interfaces
  -> theorem-body surfaces for Hilbert, H_phys, spectral theorem, PVM, observable atom
  -> compact plaquette and operator-measure compatibility
  -> exact gap theorem-body closure
  -> concrete Hilbert and H_phys realization
  -> infinite-dimensional Hilbert necessity and excitation-family support
  -> Hilbert countable basis / density / topology / completion / inner-product / instance skeletons
  -> physical unbounded-operator and concrete Yang-Mills Hamiltonian skeletons
  -> spectral realization and continuum spectral theorem skeletons
  -> final theorem release skeleton / closure / chain index / bundle manifest
  -> concrete residual closure
  -> physical Hamiltonian normalization bridge
  -> infinite-dimensional Yang-Mills realization targets
  -> infinite-dimensional residual filling bridge
  -> hard physical residual hardening map
  -> Hilbert construction lane hardening
  -> self-adjoint H_phys lane hardening
  -> continuum Yang-Mills lane hardening
  -> plaquette spectral weight lane hardening
  -> four-lane residual closure
  -> internal review residual closure gate
  -> external audit readiness gate
```

Representative source files:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean
MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalResidualFillingBridge.lean
MGAP4D/MathlibAnalytic/HardPhysicalResidualHardeningMap.lean
MGAP4D/MathlibAnalytic/HilbertConstructionLaneHardening.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean
MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean
MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean
MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean
MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
```

## CI and audit status

Full local replay is:

```bash
bash scripts/check.sh
```

The replay path currently runs:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit Hilbert construction lane hardening
[check] audit self-adjoint HPhys lane hardening
[check] audit continuum Yang-Mills lane hardening
[check] audit plaquette spectral weight lane hardening
[check] audit four-lane residual closure
[check] audit internal review residual closure gate
[check] audit external audit readiness gate
[check] replay summary
[check] lake update
[check] build external audit readiness gate
[check] lake build
```

Confirmed external-audit-readiness CI checkpoint:

```text
Workflow: Run scripts/check.sh
Run ID: 25961418682
Job ID: 76317232199
Commit checked out by CI: 7041b000c4c8f30a2d99d5429504d00cffb88bcb
Result: success
Lean-side warnings in gate build: none observed
```

That run confirmed:

```text
Lean files scanned: 457
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 8
Ordered import edges audited: 5
Lean replay summary imports: 1191
Lean replay summary declaration_like_lines: 2602
Lean replay summary namespace_lines: 938
Lean replay summary total_lines: 27203
Build completed successfully: 8368 jobs
Final lake build: 0 jobs, success
```

Current CI ledger:

```text
docs/external_audit_readiness_gate_ci.md
```

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
docs/infinite_dimensional_residual_filling_bridge.md
docs/hard_physical_residual_hardening_map.md
docs/hilbert_construction_lane_hardening.md
docs/self_adjoint_hphys_lane_hardening.md
docs/continuum_yang_mills_lane_hardening.md
docs/plaquette_spectral_weight_lane_hardening.md
docs/four_lane_residual_closure.md
docs/internal_review_residual_closure_gate.md
docs/external_audit_readiness_gate.md
docs/external_audit_readiness_gate_ci.md
```

## Review meaning

A successful replay means:

```text
the repository builds with the pinned Lean toolchain and pinned mathlib version
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-hardening, and final readiness-gate checks pass
the replay summary is reproducible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
CI output alone is a substitute for proof review
the external-audit-readiness gate is a substitute for independent replay or external audit
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
