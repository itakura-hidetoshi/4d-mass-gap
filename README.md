# MGAP4D

**MGAP4D** is Hidetoshi Itakura's GitHub-native Lean 4 repository for a normalized four-dimensional mass-gap proof architecture.

This repository is the canonical source tree for the MGAP4D line.  It contains Lean source, Lake configuration, theorem-surface maps, hard-residual ledgers, physical-normalization boundaries, audit scripts, public/external audit receipts, and independent replay instructions.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface.  KuuOS documents do not replace this repository as the canonical Lean source, and they do not independently supply external mathematical consensus.

---

## Current status as of 2026-06-10

The current `main` branch should be read through the **R1--R7 terminal / public / external audit receipt chain**.

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

Conservative public wording:

```text
MGAP4D provides a Lean 4 proof-carrying and replayable audit surface for a
normalized 4D mass-gap route.  The internal terminal R1--R7 discharge chain
carries the exact normalized value 33/20 and a positive spectral-weight witness.
External mathematical consensus and Clay-style public acceptance are separate
review processes and are not claimed by documentation alone.
```

Current reading of the proof spine:

```text
R1 concrete Hilbert closure
  -> R2 infinite-dimensional ℓ² diagonal closed/unbounded operator lane
  -> R3 adjoint/self-adjointness theorem discharge
  -> R4 genuine-PVM law-component closure
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight witness closure
  -> terminal R1--R7 discharge chain
  -> public/external audit receipt chain
```

The most compact status anchor is:

```text
docs/current_proof_status.md
```

Use this file when older pull requests, notes, or generated documentation lag behind the current proof spine.

---

## Claim boundary

This repository currently claims, at the repository-surface level:

```text
Lean 4 / Lake replay surface: present
normalized exact value carrier: exactGapValueReal = 33/20
operator/spectral derivation route: R1--R7 terminal route plus continuum-Hamiltonian route
positive spectral-weight witness: terminal-visible
R1 concrete Hilbert closure: indexed
R2 infinite ℓ² diagonal closed/unbounded operator lane: current main lane
R3 self-adjointness theorem discharge: indexed
R4 genuine-PVM law components: terminal-visible
R5 compact centered plaquette observable closure: terminal-visible
R6 non-definitional exact atom 33/20 closure: terminal-visible
R7 positive spectral-weight closure: terminal-visible
public/external audit receipt chain: present
physical-normalization boundary: explicit through E0
```

It does **not** claim by documentation alone:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing a positive scale E0
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that readiness receipts are identical to theorem bodies
that documentation or release notes are substitutes for source-level review
```

Review rule:

```text
Lean theorem bodies are the repository authority.
Documentation must track theorem bodies, not downgrade them and not overstate them.
The internal terminal R1--R7 discharge is present.
External public acceptance remains a separate review process.
The normalized value 33/20 is dimensionless until a positive physical scale E0 is chosen.
```

---

## Physical normalization

The theorem-body value is normalized and dimensionless.

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

Therefore `33/20` is the dimensionless spectral gap value of the normalized Hamiltonian surface.  A dimensional physical mass gap requires an external positive reference scale `E0`.

---

## Exact-gap layer separation

The repository separates four review layers:

```text
abstract theorem-body layer
normalized carrier layer
operator/spectral derivation layer
engineering / review-marker layer
```

Current Lean separation map:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
```

Human-readable note:

```text
docs/exact_gap_layer_separation.md
```

Important reading:

```text
Basic.lean / ExactGapReal.lean = normalized carrier layer
ConcreteR1R7ResidualDischarge.lean = current terminal derivation discharge
ContinuumHamiltonianCompleteMassGapDerivation.lean = complete Hamiltonian spectral derivation surface
YangMillsHamiltonianSpectralDerivation3320.lean = spectral derivation interface into the normalized carrier
ExactGapLayerSeparation.lean = current separation map
```

`exactGapValueReal : ℝ := 33 / 20` remains the canonical normalized carrier.  Its local `rfl` / `norm_num` checks are carrier checks.  The exact-value route is reviewed through the R1--R7 terminal route and the complete continuum-Hamiltonian spectral route, not through the carrier definition alone.

---

## Proof-debt and witness-marker inventory

External review must distinguish theorem bodies from placeholders, witnesses, receipts, and readiness packets.

Primary inventory note:

```text
docs/proof_placeholder_inventory.md
```

Inventory audit script:

```text
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

## Active Lean roots and review surfaces

Pinned toolchain / dependency lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

Top-level and high-priority review roots:

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R6/Theorem.lean
MGAP4D/R7/Theorem.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

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

A successful replay means that the pinned Lean/Lake/mathlib environment builds and that the declared audit scripts and theorem-surface checks pass locally.  It is evidence for local reproducibility.  It is not, by itself, external mathematical consensus or public problem acceptance.

---

## Recommended external review order

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `docs/current_proof_status.md`.
4. Read `THEOREM_INDEX.md`.
5. Read `EXTERNAL_AUDIT_PACKET.md`.
6. Read `INDEPENDENT_REPLAY.md`.
7. Inspect `PHYSICAL_REALIZATION_BOUNDARY.md`.
8. Inspect `docs/exact_gap_layer_separation.md`.
9. Inspect `docs/proof_placeholder_inventory.md`.
10. Inspect the R2 infinite `ℓ²` diagonal operator lane.
11. Inspect the R4 genuine-PVM law components.
12. Inspect the R5 plaquette-observable closure files.
13. Inspect the R6 exact atom `33/20` theorem bodies.
14. Inspect the R7 positive spectral-weight theorem bodies.
15. Inspect the terminal R1--R7 discharge chain and public/external audit receipt chain.
16. Record review notes append-only.

Core commands and files:

| Entry point | Role |
|---|---|
| `bash scripts/check.sh` | Complete local replay path. |
| `lake build` | Lean kernel build gate for configured roots. |
| `docs/current_proof_status.md` | Current short status anchor for `main`. |
| `THEOREM_INDEX.md` | Theorem / bridge / target surface map. |
| `EXTERNAL_AUDIT_PACKET.md` | Top-level external review packet. |
| `INDEPENDENT_REPLAY.md` | Fresh-clone replay procedure. |
| `PHYSICAL_REALIZATION_BOUNDARY.md` | Boundary for physical interpretation. |
| `docs/proof_placeholder_inventory.md` | Placeholder / witness / receipt inventory. |
| `docs/exact_gap_layer_separation.md` | Layer-separation review note. |
| `docs/r2_infinite_l2_diagonal_operator_lane.md` | R2 current lane note. |
| `docs/r4_terminal_status_supersession.md` | R4 terminal-status supersession note. |
| `docs/continuum_hamiltonian_witness_provenance.md` | Witness-slot provenance note. |

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

## Current priorities

```text
1. Keep README, ROADMAP, THEOREM_INDEX, EXTERNAL_AUDIT_PACKET, and current_proof_status synchronized.
2. Keep the R2 infinite ℓ² lane, exact-gap layer separation, and placeholder inventory visible to reviewers.
3. Refresh independent replay receipts from clean environments.
4. Confirm CI and local replay on the exact documentation / audit commit.
5. Prepare an audit-oriented version tag only after source-tree review.
6. Synchronize Zenodo only after the tag and post-tag verification receipt are stable.
7. Preserve the normalized/dimensional E0 boundary.
8. Preserve the boundary between internal Lean terminal discharge and external public acceptance.
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

The DOI-backed Zenodo record is a proof-architecture and external-audit preparation report.  It should be kept synchronized with any audit-oriented tag.

---

## Contribution and review policy

External contributions are most useful when they improve one of the following:

```text
fresh-clone replay
Lean kernel checking
theorem-body inspection
R2 infinite ℓ² closed/unbounded operator review
R4 genuine-PVM law-component review
R5 plaquette-observable closure review
R6 exact atom 33/20 review
R7 positive spectral-weight review
terminal R1--R7 discharge-chain review
public/external audit receipt review
proof-debt / placeholder inventory review
physical-normalization review
continuum-Hamiltonian review
audit-script precision
documentation consistency
external mathematical review
```

Do not treat documentation, CI ledgers, audit scripts, receipts, or release notes as substitutes for Lean kernel checking and mathematical proof review.
