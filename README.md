# MGAP4D

**MGAP4D** is a GitHub-native Lean 4 repository for developing, checking, replaying, and externally auditing the proof architecture of a normalized four-dimensional mass gap theorem.

This repository is the canonical Lean proof repository for the MGAP4D line. KuuOS may reference this repository as a physics-facing bridge and public-core governance surface, but KuuOS reference documents do not replace this repository as the canonical Lean source and do not independently open public final theorem release.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status

The current repository state records an **internal normalized theorem-body / proof-architecture surface** with explicit replay, theorem-surface audit, bridge-coherence audit, physical-Hamiltonian normalization, continuum-Hamiltonian release surfaces, complete-derivation surfaces, and external-audit-readiness support.

Inside the MGAP4D Lean proof architecture, the normalized exact spectral gap value is recorded as:

```text
exactGapValueReal = 33 / 20
Delta_norm = 33/20
```

The repository treats `33/20` as an internal normalized theorem-body value, not as a documentation artifact, CI artifact, manifest-only artifact, packaging artifact, or prototype-only release wrapper.

The current physical-Hamiltonian reading is explicitly scale-normalized:

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm

normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap

Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

In internal normalized units:

```text
E0 = 1
Delta_phys(1) = 33/20
```

Thus `33/20` is the dimensionless spectral gap of the normalized physical Hamiltonian. A dimensional physical mass gap requires an external reference scale `E0`.

## Public boundary

This repository currently claims:

```text
internal normalized theorem-body surface: present
exact normalized value surface: 33/20
physical Hamiltonian scalar normalization: present
physical Hamiltonian operator normalization: present
complete infinite-dimensional Hilbert construction lane: present
continuum-Hamiltonian theorem / release-adoption surfaces: present
complete continuum-Hamiltonian derivation surfaces: present
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
full local replay path: present
```

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI output replaces mathematical proof review
that audit scripts replace Lean kernel checking
that an external-audit-readiness gate replaces independent replay
```

The public final theorem boundary remains **review-gated** pending independent replay and external audit.

## Active Lean roots and pinned dependency lane

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

Pinned toolchain / dependency lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

The `MathlibAnalytic` root is a scoped analytic lane. It does not by itself open public final theorem release.

## Main hardening route

The current route can be read as:

```text
Exact normalized value / real positivity
  -> gap infimum / Rayleigh lower bound / Rayleigh attainment
  -> spectral mass / exact gap analytic closure
  -> Hilbert, H_phys, spectral theorem, PVM, observable interfaces
  -> compact plaquette and operator-measure compatibility
  -> exact gap theorem-body closure
  -> concrete Hilbert and H_phys realization
  -> physical Hamiltonian scalar normalization
  -> physical Hamiltonian operator normalization
  -> infinite-dimensional Yang-Mills realization targets
  -> infinite-dimensional residual filling bridge
  -> hard physical residual hardening map
  -> complete infinite-dimensional Hilbert construction
  -> Hilbert-to-physical unbounded-operator bridge
  -> self-adjoint H_phys bridge adoption
  -> self-adjoint H_phys lane hardening
  -> continuum Yang-Mills lane hardening
  -> plaquette spectral weight lane hardening
  -> continuum Hamiltonian mass-gap witness hardening
  -> continuum Hamiltonian mass-gap theorem
  -> continuum Hamiltonian mass-gap release adoption
  -> continuum Hamiltonian complete mass-gap derivation
  -> continuum Hamiltonian complete mass-gap release adoption
  -> four-lane residual closure
  -> internal review residual closure gate
  -> external audit readiness gate
```

Representative Lean files:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean
MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianOperatorNormalization.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalResidualFillingBridge.lean
MGAP4D/MathlibAnalytic/HardPhysicalResidualHardeningMap.lean
MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean
MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysBridgeAdoption.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean
MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean
MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean
MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
```

## One-command replay

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
```

The full replay path is expected to run the manifest check, forbidden-token audit, major theorem non-placeholder audit, analytic bridge-coherence audit, physical-Hamiltonian operator-normalization audit, target-layer audits, residual-hardening audits, complete Hilbert construction audit, continuum-Hamiltonian hardening audits, four-lane residual closure audit, internal review gate audit, external audit readiness audits, replay summary, selected Lean builds, and final `lake build`.

Manual Lean build:

```bash
lake update
lake build
```

## Audit scripts

| Script | Role |
|---|---|
| `scripts/verify_manifest.py` | Checks archived manifest consistency. |
| `scripts/audit_lean_forbidden_tokens.py` | Checks `sorry`, `admit`, `axiom`, and `constant` outside comments / strings. |
| `scripts/audit_major_theorem_nonplaceholder.py` | Checks named theorem surfaces for non-placeholder anchors. |
| `scripts/audit_bridge_coherence.py` | Checks analytic / physical bridge order, anchors, and public-boundary markers. |
| `scripts/audit_physical_hamiltonian_operator_normalization.py` | Checks operator-level Hamiltonian normalization anchors. |
| `scripts/audit_infinite_dimensional_target_layer.py` | Checks infinite-dimensional Yang-Mills target-obligation anchors. |
| `scripts/audit_infinite_dimensional_residual_filling.py` | Checks residual-filling bridge anchors. |
| `scripts/audit_hard_physical_residual_hardening_map.py` | Checks hard residual hardening lanes. |
| `scripts/audit_complete_infinite_dimensional_hilbert_construction.py` | Checks the complete infinite-dimensional Hilbert construction lane. |
| `scripts/audit_self_adjoint_hphys_lane_hardening.py` | Checks self-adjoint `H_phys` hardening anchors. |
| `scripts/audit_continuum_yang_mills_lane_hardening.py` | Checks continuum Yang-Mills hardening anchors. |
| `scripts/audit_plaquette_spectral_weight_lane_hardening.py` | Checks plaquette spectral-weight hardening anchors. |
| `scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py` | Checks continuum-Hamiltonian witness hardening anchors. |
| `scripts/audit_four_lane_residual_closure.py` | Checks four-lane residual closure anchors. |
| `scripts/audit_internal_review_residual_closure_gate.py` | Checks internal review residual closure gate anchors. |
| `scripts/audit_external_audit_readiness_gate.py` | Checks external audit readiness gate anchors. |
| `scripts/audit_external_audit_readiness_gate_field_classification.py` | Checks internal/external witness-field classification. |
| `scripts/audit_external_audit_readiness_replay_certificate.py` | Checks replay certificate anchors. |
| `scripts/replay_summary.py` | Generates replay summary. |
| `scripts/check.sh` | Runs the complete local replay path. |

## External review entry points

Recommended external review order:

1. `EXTERNAL_AUDIT_PACKET.md`
2. `INDEPENDENT_REPLAY.md`
3. `THEOREM_INDEX.md`
4. `PHYSICAL_REALIZATION_BOUNDARY.md`
5. `EXTERNAL_REVIEW_CHECKLIST.md`
6. `docs/external_audit_readiness_gate.md`
7. `docs/external_audit_readiness_gate_ci.md`
8. `docs/external_audit_readiness_gate_field_classification.md`
9. `docs/external_audit_readiness_replay_certificate.md`
10. `docs/physical_hamiltonian_operator_normalization.md`
11. `docs/continuum_hamiltonian_complete_release_surface.md`
12. `docs/complete_infinite_dimensional_hilbert_construction.md`
13. `docs/continuum_hamiltonian_mass_gap_witness_hardening.md`
14. `docs/four_lane_residual_closure.md`
15. `docs/internal_review_residual_closure_gate.md`

The strongest executable replay command is:

```bash
bash scripts/check.sh
```

The strongest Lean kernel gate is:

```bash
lake build
```

## What successful replay means

A successful replay means:

```text
the repository builds with the pinned Lean toolchain and pinned mathlib version
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-hardening,
physical-Hamiltonian normalization, continuum-Hamiltonian theorem/release,
final readiness-gate, field-classification, and replay-certificate checks pass
the replay summary is reproducible
```

A successful replay does **not** by itself mean:

```text
external mathematical consensus
independent peer-review acceptance
public final theorem acceptance
```

## Repository layout

```text
MGAP4D/              Active Lean source tree
MGAP4D.lean          Top-level Lean import root
docs/                Documentation, ledgers, audit packets, review surfaces
maps/                Lightweight source and dependency maps
scripts/             Local and CI audit scripts
.github/workflows/   GitHub Actions CI
CITATION.cff         Citation metadata
README.md            Repository entry point
ROADMAP.md           Current development and audit roadmap
```

## Citation

Repository citation metadata is provided in `CITATION.cff`.

```text
Title: MGAP4D: Lean 4 Proof Architecture for a Normalized 4D Mass Gap Theorem
Author: Hidetoshi Itakura
Version: v1.6-dev
DOI: 10.5281/zenodo.20181046
License: CC-BY-4.0
```

The DOI-backed Zenodo record is a proof-architecture and external-audit preparation report. It does not by itself open public final theorem release.

## Contribution and review policy

External contributions are most useful when they preserve the public boundary and improve replayability, source clarity, theorem-surface inspection, bridge-audit precision, Lean kernel checking, or independent mathematical review.

Preferred contribution types:

```text
fresh-clone replay reports
Lean build reproducibility reports
audit-script improvements
theorem-surface review notes
bridge-coherence review notes
physical-normalization boundary review
documentation corrections
external audit notes
```

Do not treat documentation, CI ledgers, or audit scripts as substitutes for Lean kernel checking and mathematical proof review.
