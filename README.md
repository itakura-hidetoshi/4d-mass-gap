# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical GitHub-native **Lean 4 / Lake** repository for a normalized four-dimensional mass-gap proof architecture.

This repository is the primary Lean source tree for the MGAP4D line.  It contains Lean theorem surfaces, theorem-body anchors, proof-spine ledgers, physical-normalization boundaries, audit scripts, review packets, and independent replay instructions.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface.  KuuOS documents do not replace this repository as the canonical Lean source tree, and they do not independently provide external mathematical consensus.

---

## Current status as of 2026-06-11

The current `main` branch should be read as an **internal Lean terminal discharge route with a public / external audit receipt surface**.

It should **not** be described as external mathematical consensus, independent peer-review completion, or Clay-style public acceptance.

The current proof-facing surface is the R1--R7 terminal / public / external audit receipt chain:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

Central Lean-facing payload:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Compact public wording:

```text
MGAP4D provides a Lean 4 proof-carrying and replayable audit surface for a
normalized 4D mass-gap route.  The internal R1--R7 terminal discharge chain
carries the exact normalized value 33/20 and a positive spectral-weight witness.
External mathematical consensus and Clay-style public acceptance remain separate
review processes.
```

For the shortest status anchor, read:

```text
docs/current_proof_status.md
```

---

## Claim boundary

This repository currently claims, at repository-surface level:

```text
Lean 4 / Lake replay surface: present
canonical normalized carrier: exactGapValueReal = 33/20
R1--R7 terminal discharge route: present
R2 current lane: infinite-dimensional ℓ² diagonal closed / unbounded operator lane
R4 genuine-PVM law-component route: terminal-visible
R5 compact centered plaquette observable route: terminal-visible
R6 non-definitional exact atom 33/20 route: terminal-visible
R7 positive spectral-weight witness route: terminal-visible
public / external audit receipt chain: present
physical-normalization boundary through E0: explicit
```

It does **not** claim by documentation alone:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing a positive scale E0
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that readiness receipts are theorem bodies unless they carry substantive typed theorem payloads
that historical StillOpen / PUnit / True markers can be ignored without classification
```

Review rule:

```text
Lean theorem bodies are the repository authority.
Documentation must track theorem bodies: neither downgrade terminal Lean surfaces nor overstate them.
External public acceptance remains a separate review process.
```

---

## Current proof spine

The current proof spine should be read as:

```text
R1 concrete Hilbert closure
  -> R2 infinite-dimensional ℓ² diagonal closed / unbounded operator lane
  -> R3 adjoint / self-adjointness theorem discharge
  -> R4 genuine-PVM law-component closure
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight witness closure
  -> terminal R1--R7 discharge chain
  -> public / external audit receipt chain
```

Important review anchors:

| Surface | Anchor |
|---|---|
| Top-level import root | `MGAP4D.lean` |
| Analytic root | `MGAP4D/MathlibAnalytic.lean` |
| Current status anchor | `docs/current_proof_status.md` |
| R2 current lane | `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean` |
| Exact-gap layer separation | `MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean` |
| Complete Hamiltonian route | `MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean` |
| Yang--Mills spectral derivation interface | `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean` |
| R4 theorem surface | `MGAP4D/R4/TheoremSurface.lean` |
| R5 theorem surface | `MGAP4D/R5/TheoremSurface.lean` |
| R6 exact atom | `MGAP4D/R6/Theorem.lean` |
| R7 positive weight | `MGAP4D/R7/Theorem.lean` |
| Terminal discharge chain | `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` |
| External audit receipt chain | `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean` |
| Placeholder / witness inventory | `docs/proof_placeholder_inventory.md` |
| R4 supersession note | `docs/r4_terminal_status_supersession.md` |

Representative terminal theorem:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Representative R7 payload:

```lean
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
  observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  witnessSector = orthogonal ∧ witnessSector ≠ vacuum
```

---

## Physical normalization

The value `33/20` is the normalized, dimensionless theorem-body value.

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

A dimensional physical mass gap therefore requires an external positive reference scale `E0`.

---

## Layer separation

External review should keep four layers separate:

```text
abstract theorem-body layer
normalized carrier layer
operator / spectral derivation layer
engineering / review-marker layer
```

Current map:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
docs/exact_gap_layer_separation.md
```

Reading guide:

```text
Basic.lean / ExactGapReal.lean = normalized carrier layer
ConcreteR1R7ResidualDischarge.lean = current terminal derivation discharge
ContinuumHamiltonianCompleteMassGapDerivation.lean = complete Hamiltonian spectral derivation surface
YangMillsHamiltonianSpectralDerivation3320.lean = spectral derivation interface into the normalized carrier
ExactGapLayerSeparation.lean = current separation map
```

`exactGapValueReal` is the canonical normalized carrier defined through `fourDYangMillsAnalyticGapValue`; the local `33/20` check is a carrier-level normalization, while the review route is the R1--R7 terminal chain plus the complete continuum-Hamiltonian spectral route.

---

## Proof-debt and witness-marker inventory

External reviewers must distinguish theorem bodies from placeholders, witnesses, receipts, readiness packets, and historical markers.

Primary inventory:

```text
docs/proof_placeholder_inventory.md
scripts/audit_proof_placeholder_inventory.py
```

Current rule:

```text
PUnit, True, and StillOpen are open proof-debt markers unless they have been
replaced, discharged, or explicitly superseded by typed theorem anchors.
Readiness markers such as theoremWitnessOnly, receipt, ready, prototype,
skeleton, boundary, packet, and manifest are review-order evidence unless their
payload is a substantive typed theorem.
```

Historical `StillOpen` markers must be classified as historical or explicitly superseded before they can coexist with a terminal closure reading.

---

## Replay

Pinned lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

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

A successful replay means that the pinned Lean / Lake / mathlib environment builds and that the declared audit scripts and theorem-surface checks pass locally.  It is reproducibility evidence, not external mathematical consensus by itself.

---

## External review order

Recommended first-pass review order:

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `docs/current_proof_status.md`.
4. Read `THEOREM_INDEX.md`.
5. Read `EXTERNAL_AUDIT_PACKET.md`.
6. Read `INDEPENDENT_REPLAY.md`.
7. Inspect `PHYSICAL_REALIZATION_BOUNDARY.md`.
8. Inspect `docs/exact_gap_layer_separation.md`.
9. Inspect `docs/proof_placeholder_inventory.md`.
10. Inspect `docs/r2_infinite_l2_diagonal_operator_lane.md`.
11. Inspect `docs/r4_terminal_status_supersession.md`.
12. Inspect the R4 genuine-PVM law components.
13. Inspect the R5 plaquette-observable closure.
14. Inspect the R6 exact atom `33/20` theorem bodies.
15. Inspect the R7 positive-weight theorem bodies.
16. Inspect the terminal R1--R7 discharge chain and public / external audit receipt chain.
17. Record review notes append-only.

---

## Repository layout

```text
MGAP4D/              Active Lean source tree
MGAP4D.lean          Top-level Lean import root
docs/                Documentation, ledgers, audit packets, review surfaces
maps/                Source and dependency maps
scripts/             Local and CI audit scripts
.github/workflows/   GitHub Actions CI
CITATION.cff         Citation metadata
README.md            Repository entry point
ROADMAP.md           Review and audit roadmap
```

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized.
2. Keep the R2 infinite `ℓ²` lane visible as the current main R2 reading.
3. Keep exact-gap layer separation visible to prevent carrier / derivation confusion.
4. Keep placeholder, witness, and proof-debt inventory visible.
5. Refresh independent replay receipts from clean environments.
6. Confirm CI and local replay on the documentation / audit-synchronization commit.
7. Prepare an audit-oriented version tag only after source-tree review.
8. Synchronize Zenodo only after the tag and post-tag verification receipt are stable.
9. Preserve the normalized / dimensional `E0` boundary.
10. Preserve the boundary between internal Lean terminal discharge and external public acceptance.

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

The DOI-backed Zenodo record is an archival / reproducibility snapshot.  The current repository state, CI status, and external review boundary should be checked in GitHub before citing the latest development state.

---

## Contribution and review policy

External contributions are most useful when they improve one of the following:

```text
fresh-clone replay
Lean build reproducibility
theorem-surface review
source-tree clarity
placeholder / witness-marker classification
physical-normalization boundary clarity
external mathematical review notes
audit script precision
public-boundary accuracy
```

Do not treat documentation, CI ledgers, receipts, or audit scripts as substitutes for Lean kernel checking and mathematical proof review.
