# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical GitHub-native **Lean 4 / Lake** repository for a normalized four-dimensional mass-gap proof architecture.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. It does not replace this repository as the canonical Lean source tree, and it does not independently supply external mathematical consensus.

---

## Current status as of 2026-06-11

The current `main` branch should be read as an **internal Lean replay / terminal-audit surface** for a normalized 4D mass-gap route.

It should **not** be described as:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final acceptance
a complete public solution of the 4D Yang--Mills mass-gap problem
```

The present state is more precise:

```text
Lean 4 / Lake repository foundation: present
Basic-layer route marker: present
abstract normalized real carrier: present
pre-R6 Hamiltonian / PVM / spectral carrier-alignment route: present
R6 spectral/PVM value-pinning lane for 33/20: present
R7 positive spectral-weight witness lane: present
R1--R7 terminal audit chain: present
public / external audit receipt surface: present
placeholder / witness / proof-debt inventory: active review layer
external mathematical acceptance: not claimed
```

Compact public wording:

```text
MGAP4D provides a Lean 4 proof-carrying and replayable audit surface for a
normalized 4D mass-gap route. The internal R1--R7 terminal chain records the
exact normalized value 33/20 and a positive spectral-weight witness, while
external mathematical consensus and Clay-style public acceptance remain separate
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
canonical Lean 4 / Lake replay surface
Mathlib-backed analytic branch
Basic-layer marker showing that the numeric carrier is absent there
abstract downstream normalized carrier exactGapValueReal
pre-R6 spectral alignment of exactGapValueReal with a derived Hamiltonian spectral value
R6 spectral/PVM pinning of the derived value to 33/20
R7 preservation of exact value plus positive spectral weight
R1--R7 terminal audit-chain projection of exact 33/20 plus positive weight
explicit final-release hold and public-boundary lock
normalized / dimensional E0 boundary
proof-debt inventory for PUnit / True / StillOpen / witness / receipt markers
```

It does **not** claim by documentation alone:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing a positive external scale E0
that Basic.lean carries the numerical mass-gap value
that ExactGapReal.lean itself proves exactGapValueReal = 33/20
that carrier-level arithmetic replaces the Hamiltonian/PVM/spectral route
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that receipt / ready / witness-only records are theorem bodies by themselves
that historical or active StillOpen / PUnit / True markers can be ignored
```

Review rule:

```text
Lean theorem bodies are the repository authority.
Documentation must track theorem bodies without upgrading receipts into proofs.
External public acceptance remains a separate review process.
```

---

## Current proof spine

The current proof spine should be read as layered, not as a single definitional unfolding:

```text
Basic-layer route marker
  -> downstream abstract normalized real carrier exactGapValueReal
  -> continuum-Hamiltonian / PVM / operator-spectral carrier alignment
  -> R6 non-definitional spectral/PVM exact-atom pinning route for 33/20
  -> R7 positive spectral-weight witness route
  -> R1--R7 terminal audit chain
  -> public / external audit receipt chain
```

Important review anchors:

| Surface | Anchor |
|---|---|
| Top-level import root | `MGAP4D.lean` |
| Analytic root | `MGAP4D/MathlibAnalytic.lean` |
| Current status anchor | `docs/current_proof_status.md` |
| Basic-layer route marker | `MGAP4D/MathlibAnalytic/Basic.lean` |
| Abstract real carrier | `MGAP4D/MathlibAnalytic/ExactGapReal.lean` |
| Exact-gap layer separation | `MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean` |
| Human-readable layer note | `docs/exact_gap_layer_separation.md` |
| Continuum Hamiltonian theorem surface | `MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean` |
| Complete Hamiltonian route | `MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean` |
| Yang--Mills spectral interface | `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean` |
| R2 current infinite `ℓ²` lane | `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean` |
| R4 theorem surface | `MGAP4D/R4/TheoremSurface.lean` |
| R5 theorem surface | `MGAP4D/R5/TheoremSurface.lean` |
| R6 exact atom route | `MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean` |
| R7 positive weight route | `MGAP4D/R7/Theorem.lean` |
| Terminal R1--R7 chain | `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` |
| External audit receipt chain | `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean` |
| Placeholder / witness inventory | `docs/proof_placeholder_inventory.md` |
| R4 supersession note | `docs/r4_terminal_status_supersession.md` |
| R2 lane note | `docs/r2_infinite_l2_diagonal_operator_lane.md` |

Representative Basic-layer marker:

```lean
theorem four_d_yang_mills_basic_layer_numeric_carrier_absent :
    fourDYangMillsAnalyticGapValueOrigin.basicLayerNumericCarrierAbsent = true
```

Representative abstract-carrier facts:

```lean
theorem exactGapValueReal_pos : 0 < exactGapValueReal

theorem exactGapValueReal_above_one : 1 < exactGapValueReal
```

Representative pre-R6 spectral alignment:

```lean
theorem yang_mills_hamiltonian_exact_gap_eq_spectral_value :
    exactGapValueReal =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue
```

Representative R6 value-pinning theorem:

```lean
theorem exact_atom_3320_r6_exact_gap_value_eq_3320
    (h : ExactAtom3320R6SpectralPVMPinsDerivedValue) :
    exactGapValueReal = (33 : ℝ) / 20
```

Representative terminal projection:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

---

## Exact-gap layer separation

External review should keep these layers separate:

```text
1. Basic-layer route marker
2. downstream abstract real-carrier / positivity-boundary layer
3. continuum-Hamiltonian / PVM / operator-spectral carrier-alignment layer
4. R6 exact atom and R7 positive spectral-weight route
5. engineering / audit / public-boundary marker layer
```

Current reading:

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as an abstract downstream normalized real carrier
  -> proves positivity and above-one facts
  -> does not provide exactGapValueReal_eq
  -> does not expose exactGapValueReal = 33/20

YangMillsHamiltonianSpectralDerivation3320.lean
  -> aligns spectral infimum / attainment / observable atom values with exactGapValueReal
  -> aligns exactGapValueReal with the derived Hamiltonian spectral value
  -> intentionally does not export derivedHamiltonianSpectralValue = 33/20 outside R6

R6 exact-atom layer
  -> pins the displayed value 33/20 through the spectral/PVM atom lane
  -> prevents the value from being read as pre-R6 definitional unfolding

R7 / terminal chain
  -> carries exact 33/20 plus positive spectral weight to the terminal audit surface
```

Current map:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
docs/exact_gap_layer_separation.md
```

---

## Physical normalization

The value `33/20` is a normalized, dimensionless theorem-body value at the internal audit surface.

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

Historical `StillOpen` markers must be classified as historical or explicitly superseded before they can coexist with a terminal-chain reading.

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

A successful replay means that the pinned Lean / Lake / mathlib environment builds and that the declared audit scripts and theorem-surface checks pass locally. It is reproducibility evidence, not external mathematical consensus by itself.

---

## External review order

Recommended first-pass review order:

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `docs/current_proof_status.md`.
4. Read `docs/exact_gap_layer_separation.md`.
5. Read `docs/proof_placeholder_inventory.md`.
6. Read `THEOREM_INDEX.md`.
7. Read `EXTERNAL_AUDIT_PACKET.md`.
8. Read `INDEPENDENT_REPLAY.md`.
9. Inspect `PHYSICAL_REALIZATION_BOUNDARY.md`.
10. Inspect `docs/r2_infinite_l2_diagonal_operator_lane.md`.
11. Inspect `docs/r4_terminal_status_supersession.md`.
12. Inspect the Basic / ExactGapReal / Yang--Mills spectral derivation / R6 / R7 separation.
13. Inspect R2, R4, R5, R6, and R7 theorem surfaces.
14. Inspect the terminal R1--R7 discharge chain and public / external audit receipt chain.
15. Record review notes append-only.

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
2. Keep the Basic / ExactGapReal / spectral-derivation / R6-R7 layer separation visible.
3. Keep the R2 infinite `ℓ²` lane visible as the current main R2 reading.
4. Keep placeholder, witness, and proof-debt inventory visible.
5. Resolve or explicitly supersede `PUnit`, `True`, and `StillOpen` markers before using any lane as final analytic closure.
6. Refresh independent replay receipts from clean environments.
7. Confirm CI and local replay on the documentation / audit-synchronization commit.
8. Prepare an audit-oriented version tag only after source-tree review.
9. Synchronize Zenodo only after the tag and post-tag verification receipt are stable.
10. Preserve the normalized / dimensional `E0` boundary.
11. Preserve the boundary between internal Lean terminal audit discharge and external public acceptance.

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

The DOI-backed Zenodo record is an archival / reproducibility snapshot. The current repository state, CI status, and external review boundary should be checked in GitHub before citing the latest development state.

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
exact-gap layer-separation clarity
external mathematical review notes
audit script precision
public-boundary accuracy
```

Do not treat documentation, CI ledgers, receipts, or audit scripts as substitutes for Lean kernel checking and mathematical proof review.
