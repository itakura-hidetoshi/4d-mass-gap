# MGAP4D

**MGAP4D** is the canonical Lean 4 repository for the normalized four-dimensional mass gap proof architecture maintained by Hidetoshi Itakura.

This repository is not a general physics essay and not a KuuOS documentation mirror. It is the GitHub-native replay surface for the MGAP4D line: Lean source, Lake configuration, theorem-surface maps, audit scripts, physical-normalization ledgers, external-review packets, and independent replay instructions are kept in one source tree.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS documents do not replace this repository as the canonical Lean source, and they do not independently open public final theorem release.

---

## Status as of 2026-05-31

The current `main` branch records an **internal normalized Lean theorem-body / proof-architecture surface** for a normalized 4D mass gap route.

The active route includes:

```text
Lean 4 / Lake replay surface
exact normalized theorem-body value
physical Hamiltonian scalar normalization
physical Hamiltonian operator normalization
complete infinite-dimensional Hilbert construction lane
Hilbert-to-physical unbounded-operator bridge
self-adjoint H_phys lane hardening
continuum Yang-Mills lane hardening
plaquette spectral-weight lane hardening
continuum-Hamiltonian theorem surfaces
continuum-Hamiltonian complete derivation surfaces
finite-carrier Mathlib seed ladder over Fin 2 / Fin 3
four-lane residual closure
internal review residual closure gate
external audit readiness gate
one-command local replay path
```

The normalized theorem-body value recorded by the Lean route is:

```text
exactGapValueReal = 33 / 20
Delta_norm = 33/20
```

This repository treats `33/20` as an **internal normalized theorem-body value**. It is not treated as a documentation artifact, CI artifact, manifest-only artifact, release-wrapper artifact, or prototype-only assertion.

The public final theorem boundary remains review-gated until independent replay and external mathematical review have been completed.

Recommended public wording:

```text
MGAP4D provides a Lean 4 proof architecture and replayable audit surface
for an internal normalized 4D mass gap theorem-body route with normalized value 33/20.
The repository is prepared for independent replay and external review.
Public final theorem acceptance is not claimed.
```

---

## Claim boundary

This repository currently claims:

```text
internal normalized theorem-body surface: present
exact normalized value surface: 33/20
physical Hamiltonian scalar normalization: present
physical Hamiltonian operator normalization: present
complete infinite-dimensional Hilbert construction lane: present
Hilbert-to-physical unbounded-operator bridge: present
self-adjoint H_phys lane hardening: present
continuum Yang-Mills lane hardening: present
plaquette spectral-weight lane hardening: present
continuum-Hamiltonian theorem and release-adoption surfaces: present
continuum-Hamiltonian complete derivation surfaces: present
finite-carrier Mathlib seed ladder over Fin 2 / Fin 3: present
general Fin n / basis / dense-span / operator / spectral boundary: held
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
fresh-clone replay procedure: present
```

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that external-audit readiness equals external audit
that finite-carrier Fin 2 / Fin 3 seeds imply the full general Fin n / basis / dense-span / operator / spectral theorem chain
```

Review principle:

```text
Lean kernel checking is necessary but not identical with external mathematical consensus.
Replay success is evidence, not peer review.
External-audit readiness is a gate, not the external audit itself.
Documentation must never be treated as a substitute for theorem bodies.
```

---

## Physical normalization

The normalized theorem-body value is dimensionless.

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

Therefore `33/20` is the dimensionless spectral gap value of the normalized physical-Hamiltonian surface. A dimensional physical mass gap requires an external positive reference scale `E0`.

---

## Active Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

Pinned toolchain / dependency lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

`MGAP4D/MathlibAnalytic.lean` is the scoped analytic root for the current theorem-surface route. It does not by itself open public final theorem release.

---

## One-command replay

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
```

Manual Lean build:

```bash
lake update
lake build
```

A successful replay means that the pinned Lean/Lake/mathlib environment builds and that the declared audit scripts, theorem-surface checks, bridge checks, physical-normalization checks, continuum-Hamiltonian checks, and external-readiness checks pass.

A successful replay does **not** by itself mean external mathematical consensus, peer-review completion, or public final theorem acceptance.

---

## Current proof route

The current route is organized as:

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
  -> finite-carrier Mathlib seed ladder summary
  -> four-lane residual closure
  -> internal review residual closure gate
  -> external audit readiness gate
```

Representative Lean files:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianOperatorNormalization.lean
MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean
MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean
MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean
MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean
MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
```

For a full theorem-surface map, start with `THEOREM_INDEX.md`.

---

## Audit and review entry points

Recommended external review order:

1. Run `bash scripts/check.sh`.
2. Run `lake build`.
3. Read `EXTERNAL_AUDIT_PACKET.md`.
4. Read `INDEPENDENT_REPLAY.md`.
5. Inspect the major theorem surfaces in `THEOREM_INDEX.md`.
6. Inspect the physical normalization boundary in `PHYSICAL_REALIZATION_BOUNDARY.md`.
7. Inspect the continuum-Hamiltonian complete release surface in `docs/continuum_hamiltonian_complete_release_surface.md`.
8. Inspect the external-audit readiness gate documents in `docs/`.
9. Record review notes append-only.

Important commands and files:

| Entry point | Role |
|---|---|
| `bash scripts/check.sh` | Complete local replay path. |
| `lake build` | Strongest Lean kernel build gate. |
| `THEOREM_INDEX.md` | Theorem / bridge / target surface map. |
| `EXTERNAL_AUDIT_PACKET.md` | Top-level external review packet. |
| `INDEPENDENT_REPLAY.md` | Fresh-clone replay procedure. |
| `PHYSICAL_REALIZATION_BOUNDARY.md` | Boundary for physical interpretation. |
| `docs/external_audit_readiness_gate.md` | External-audit readiness ledger. |
| `docs/external_audit_readiness_replay_certificate.md` | Replay certificate ledger. |

Core audit scripts:

| Script | Role |
|---|---|
| `scripts/verify_manifest.py` | Checks archived manifest consistency. |
| `scripts/audit_lean_forbidden_tokens.py` | Checks forbidden Lean tokens outside comments / strings. |
| `scripts/audit_major_theorem_nonplaceholder.py` | Checks major theorem surfaces for required non-placeholder anchors. |
| `scripts/audit_bridge_coherence.py` | Checks bridge order, anchors, and public-boundary markers. |
| `scripts/audit_physical_hamiltonian_operator_normalization.py` | Checks operator-level Hamiltonian normalization anchors. |
| `scripts/audit_complete_infinite_dimensional_hilbert_construction.py` | Checks the complete infinite-dimensional Hilbert construction lane. |
| `scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py` | Checks continuum-Hamiltonian witness hardening anchors. |
| `scripts/audit_four_lane_residual_closure.py` | Checks four-lane residual closure anchors. |
| `scripts/audit_internal_review_residual_closure_gate.py` | Checks internal review residual closure gate anchors. |
| `scripts/audit_external_audit_readiness_gate.py` | Checks external audit readiness gate anchors. |
| `scripts/audit_external_audit_readiness_replay_certificate.py` | Checks replay certificate anchors. |
| `scripts/replay_summary.py` | Generates replay summary. |

---

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
ROADMAP.md           Development and audit roadmap
```

---

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

---

## Contribution and review policy

External contributions are most useful when they improve one of the following:

```text
fresh-clone replay
Lean kernel checking
theorem-surface inspection
bridge-coherence review
physical-normalization review
continuum-Hamiltonian review
finite-carrier ladder review
audit-script precision
documentation consistency
external mathematical review
```

Do not treat documentation, CI ledgers, or audit scripts as substitutes for Lean kernel checking and mathematical proof review.
