# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical GitHub-native **Lean 4 / Lake** repository for a normalized four-dimensional Yang--Mills mass-gap proof architecture.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. It does not replace this repository as the canonical Lean source tree, and it does not independently supply external mathematical consensus.

---

## Current status as of 2026-06-12

The current `main` branch should be read as a **Lean replay / internal terminal-audit surface**, not as external mathematical acceptance.

Two proof-facing surfaces are visible:

```text
A. normalized exact-gap audit route
   Basic marker
     -> abstract normalized carrier exactGapValueReal
     -> Hamiltonian / PVM / spectral carrier alignment
     -> R6 exact-atom value pinning for 33/20
     -> R7 positive spectral-weight witness
     -> R1--R7 terminal audit chain
     -> public / external audit receipt chain

B. axiomatic / OS-Wightman / Euclidean construction route
   axiomatic closure target
     -> OS/Wightman Hamiltonian reconstruction spine
     -> OS/Wightman mass-gap definition bridge
     -> OS/Wightman external audit bridge
     -> Euclidean measure to mass-gap pipeline
     -> Euclidean measure unconditional-construction target
     -> finite-volume / continuum construction spine
     -> Euclidean construction external audit bridge
     -> ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
```

The repository does **not** claim external consensus, independent peer-review completion, public final acceptance, an externally accepted OS/Wightman bridge, an externally accepted construction-spine external-audit projection, or an unconditional construction of the physical four-dimensional Yang--Mills measure from first principles.

Boundary anchor: external acceptance of the construction-spine external-audit projection is not claimed.

Compact public wording:

```text
MGAP4D provides a Lean 4 proof-carrying and replayable audit surface for a
normalized 4D mass-gap route. The internal R1--R7 terminal chain records the
normalized value 33/20 and a positive spectral-weight witness. The repository
also contains conditional axiomatic / OS-Wightman / Euclidean-construction bridge
surfaces, including a finite-volume/continuum construction spine and a
construction-spine external-audit projection. External mathematical consensus
and public acceptance remain separate review processes.
```

For the shortest status anchor, read `docs/current_proof_status.md`.

---

## Claim boundary

This repository currently exposes:

```text
canonical Lean 4 / Lake replay surface
Mathlib-backed analytic branch
Basic-layer marker showing that the numeric carrier is absent there
abstract downstream normalized carrier exactGapValueReal
Hamiltonian / PVM / spectral carrier-alignment route
R6 spectral/PVM value-pinning lane for 33/20
R7 positive spectral-weight witness lane
R1--R7 terminal audit projection of exact 33/20 plus positive weight
OS/Wightman and Euclidean construction bridge surfaces
Euclidean measure unconditional-construction target
finite-volume/continuum construction spine
construction-spine external-audit projection
normalized / dimensional E0 boundary
proof-debt inventory for PUnit / True / StillOpen / witness / receipt markers
```

It does **not** claim by documentation alone that `Basic.lean` or `ExactGapReal.lean` proves the final numeric value, that audit scripts replace Lean checking, that receipt / ready / witness-only records are theorem bodies by themselves, or that construction-spine external-audit projection equals external acceptance.

Review rule:

```text
Lean theorem bodies are the repository authority.
Documentation must track theorem bodies without upgrading receipts into proofs.
External public acceptance remains a separate review process.
```

---

## Current proof-facing spine

```text
Basic-layer route marker
  -> downstream abstract normalized real carrier exactGapValueReal
  -> continuum-Hamiltonian / PVM / operator-spectral carrier alignment
  -> R6 non-definitional spectral/PVM exact-atom pinning route for 33/20
  -> R7 positive spectral-weight witness route
  -> R1--R7 terminal audit chain
```

The newer OS/Wightman / Euclidean route records conditional theorem targets and construction-spine audit projections. The remaining hard task there is the concrete construction and external validation of the physical four-dimensional Yang--Mills measure and reconstruction spine.

OS/Wightman--Euclidean theorem-facing route:

```text
EuclideanYangMillsFiniteVolumeApproximation
  -> EuclideanYangMillsContinuumMeasureConstructionSpine
  -> EuclideanYangMillsMeasureUnconditionalConstructionTarget
  -> EuclideanYangMillsMeasureMassGapPipeline
  -> OSWightmanMassGapDefinitionBridge
  -> ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
  -> ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
```

---

## Important review anchors

| Surface | Anchor |
|---|---|
| Top-level import root | `MGAP4D.lean` |
| Analytic root | `MGAP4D/MathlibAnalytic.lean` |
| Current status anchor | `docs/current_proof_status.md` |
| Basic-layer route marker | `MGAP4D/MathlibAnalytic/Basic.lean` |
| Abstract real carrier | `MGAP4D/MathlibAnalytic/ExactGapReal.lean` |
| Exact-gap layer note | `docs/exact_gap_layer_separation.md` |
| Yang--Mills spectral interface | `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean` |
| R6 exact atom route | `MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean` |
| R7 positive weight route | `MGAP4D/R7/Theorem.lean` |
| Terminal R1--R7 chain | `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` |
| Axiomatic / OS-Wightman / Euclidean route note | `docs/axiomatic_yang_mills_mass_gap_closure.md` |
| OS/Wightman definition bridge | `MGAP4D/MathlibAnalytic/OSWightmanMassGapDefinitionBridge.lean` |
| OS/Wightman external audit bridge | `MGAP4D/MathlibAnalytic/OSWightmanMassGapExternalAuditBridge.lean` |
| Euclidean measure pipeline | `MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureToMassGapPipeline.lean` |
| Euclidean unconditional target | `MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureUnconditionalTarget.lean` |
| Euclidean construction spine | `MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionSpine.lean` |
| Euclidean construction external audit bridge | `MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean` |
| Placeholder / witness inventory | `docs/proof_placeholder_inventory.md` |

Representative current theorem anchors:

```lean
theorem four_d_yang_mills_basic_layer_numeric_carrier_absent :
    fourDYangMillsAnalyticGapValueOrigin.basicLayerNumericCarrierAbsent = true

theorem exactGapValueReal_pos : 0 < exactGapValueReal

theorem exactGapValueReal_above_one : 1 < exactGapValueReal

theorem yang_mills_hamiltonian_exact_gap_eq_spectral_value :
    exactGapValueReal =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue

theorem exact_atom_3320_r6_exact_gap_value_eq_3320_ready :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20

theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true

theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap

theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection

theorem external_audit_readiness_euclidean_construction_spine_exact_gap_positive

theorem external_audit_readiness_euclidean_construction_spine_exact_gap_threshold

theorem external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation
```

---

## Exact-gap layer separation

```text
Basic.lean
  -> marker-only route-deferred layer, no real-valued carrier

ExactGapReal.lean
  -> abstract normalized real carrier, positivity and above-one facts only

R6 exact-atom layer
  -> pins 33/20 through the Hamiltonian/PVM/spectral atom lane

R7 / terminal chain
  -> carries exact 33/20 plus positive spectral weight to terminal audit level

Axiomatic / Euclidean construction layer
  -> conditional bridge and construction-target material, not an unconditional construction by itself
```

---

## Physical normalization

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

In internal normalized units, `E0 = 1`. A dimensional physical mass gap requires an external positive reference scale `E0`.

---

## Proof-debt and witness-marker inventory

```text
Primary inventory: docs/proof_placeholder_inventory.md
Companion script: scripts/audit_proof_placeholder_inventory.py
```

`PUnit`, `True`, and `StillOpen` remain proof-debt markers unless replaced or explicitly superseded by typed theorem anchors. A terminal-looking chain is therefore a review route, not an automatic substitute for dependency review.

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

The OS/Wightman--Euclidean replay stages include:

```text
[check] audit OS/Wightman mass-gap bridge
[check] build OS/Wightman mass-gap external audit bridge
[check] build Euclidean Yang-Mills measure to mass-gap pipeline
[check] build unconditional Euclidean Yang-Mills measure target
[check] build Euclidean Yang-Mills measure construction spine
[check] build Euclidean Yang-Mills construction external audit bridge
```

Manual route for this lane:

```bash
lake build MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge
```

Manual full Lean build:

```bash
lake update
lake build
```

A successful replay means that the pinned Lean / Lake / mathlib environment builds and that the declared audit scripts and theorem-surface checks pass locally. It is reproducibility evidence, not external mathematical consensus by itself.

---

## External review order

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `docs/current_proof_status.md`.
4. Read `docs/exact_gap_layer_separation.md`.
5. Read `docs/axiomatic_yang_mills_mass_gap_closure.md`.
6. Read `docs/proof_placeholder_inventory.md`.
7. Read `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and `INDEPENDENT_REPLAY.md`.
8. Inspect the Basic / ExactGapReal / Yang--Mills spectral derivation / R6 / R7 separation.
9. Inspect the OS/Wightman and Euclidean construction bridge files.
10. Inspect `EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean` and confirm it is a review-routing projection, not external acceptance.
11. Inspect the terminal R1--R7 discharge chain and public / external audit receipt chain.

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `docs/exact_gap_layer_separation.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and `INDEPENDENT_REPLAY.md` synchronized.
2. Keep the Basic / ExactGapReal / spectral-derivation / R6-R7 layer separation visible.
3. Keep the OS/Wightman and Euclidean construction bridge status visible as conditional / construction-target material.
4. Keep the construction-spine external-audit projection visible as a review-routing surface, not external acceptance.
5. Keep placeholder, witness, and proof-debt inventory visible.
6. Keep final-release hold, public-boundary lock, and external-acceptance boundary explicit.
