# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical **MGAP4D Lean proof repository**.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. It does not replace this repository as the canonical Lean proof repository and does not independently supply external mathematical consensus.

---

## Status snapshot as of 2026-06-12

Current `main` should be read as an **internal Lean replay / terminal-audit surface**, not as external mathematical acceptance.

```text
normalized R1--R7 terminal audit route: present
exact normalized value 33/20 at terminal audit level: present
positive spectral-weight witness at terminal audit level: present
OS/Wightman mass-gap bridge: present
Euclidean measure to mass-gap pipeline: present
Euclidean measure unconditional-construction target: present
finite-volume / continuum construction spine: present
construction-spine external-audit projection: present
ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection: present
placeholder / witness / proof-debt inventory: active
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed
unconditional physical Yang--Mills measure construction: not claimed
external acceptance of the construction-spine external-audit projection: not claimed
```

Central normalized terminal-audit payload:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Layer-correct reading:

```text
Basic.lean
  -> route-deferred marker only
  -> no real-valued gap carrier
  -> no final-value literal

ExactGapReal.lean
  -> downstream abstract normalized real carrier exactGapValueReal
  -> positivity and above-one facts only
  -> no exposed exactGapValueReal = 33/20 equality

Continuum Hamiltonian / PVM / spectral route
  -> aligns exactGapValueReal with a derived Hamiltonian spectral value
  -> keeps final-value adoption gated to R6

R6
  -> non-definitional exact-atom / spectral-PVM value-pinning route for 33/20

R7
  -> positive spectral-weight witness and preservation of exact value

R1--R7 terminal chain
  -> terminal audit projection of exact 33/20 plus positive spectral weight

Axiomatic / OS-Wightman / Euclidean construction route
  -> conditional closure targets and external audit projections
  -> construction-spine external-audit projection, not external acceptance by itself
```

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

Physical normalization boundary:

```text
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
internal units: E0 = 1, Delta_phys(1) = 33/20
```

Short status anchor:

```text
docs/current_proof_status.md
```

---

## Roadmap posture

The project should not move by adding decorative theorem phases. The active work is now:

```text
repository / documentation synchronization
fresh-clone independent replay
source-tree dependency review
placeholder / witness / proof-debt classification
OS/Wightman and Euclidean construction bridge review
construction-spine external-audit projection review
external mathematical review
audit-oriented version tagging
Zenodo synchronization after a stable tag and replay receipt
```

New work should directly support replayability, theorem-surface clarity, proof-debt classification, exact-gap layer separation, OS/Wightman / Euclidean bridge clarity, construction-spine external-audit projection clarity, external review, or public-boundary accuracy.

---

## Installed lanes and review status

### A. Repository foundation

Status: **installed / active**

- [x] GitHub-native Lean 4 / Lake repository foundation.
- [x] Pinned Lean / mathlib lane.
- [x] `MGAP4D.lean` top-level root.
- [x] `MGAP4D/MathlibAnalytic.lean` analytic theorem-surface root.
- [x] GitHub Actions workflows.
- [x] `scripts/check.sh` one-command replay path.
- [ ] Keep replay receipts current after each proof-surface change.

### B. Basic marker, real carrier, and physical boundary

Status: **installed as separated layers; active as review discipline**

- [x] Keep `Basic.lean` as the route-deferred marker layer with no real-valued gap carrier.
- [x] Keep `ExactGapReal.lean` as the downstream abstract normalized real carrier layer.
- [x] Record positivity and above-one facts for `exactGapValueReal`.
- [x] Keep `exactGapValueReal = 33/20` out of `ExactGapReal.lean`.
- [x] Preserve the normalized / dimensional distinction through `E0`.

### C. Exact-gap layer separation

Status: **installed as separation map; active as review discipline**

- [x] Separate Basic marker, downstream real carrier, operator / spectral derivation, R6/R7 route, and engineering / audit-marker layers.
- [x] Add Lean separation map and human-readable review note.
- [x] Keep documentation from implying that `Basic.lean` or `ExactGapReal.lean` alone supplies the final numerical value.
- [x] Keep documentation from downgrading the terminal R1--R7 exact-value and positive-weight surface.

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
docs/exact_gap_layer_separation.md
```

### D. R1--R3 analytic substrate

Status: **installed; dependency-audit remains active**

- [x] R1 concrete Hilbert closure surface.
- [x] R2 infinite-dimensional `ℓ²` diagonal closed / unbounded operator lane.
- [x] R2-to-R3 input handoff.
- [x] R2-to-spectral-input handoff.
- [x] R3 adjoint / self-adjointness theorem discharge surface.
- [ ] Review every `ready`, `True`, `PUnit`, and handoff object before using this lane as final analytic closure.

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean
docs/r2_infinite_l2_diagonal_operator_lane.md
```

### E. R4 genuine-PVM law components

Status: **installed; historical-marker supersession audit remains active**

- [x] Actual Borel carrier surface.
- [x] Empty / whole / complement / union / intersection laws.
- [x] Operator-topology countable-additivity / convergence receipt.
- [x] No-shell-collapse boundary.
- [x] R4 handoff into R5, R6, and R7.
- [ ] Keep every historical `StillOpen` occurrence classified as active, historical, or superseded.

### F. R5 compact centered plaquette observable

Status: **installed in the hard-physical-residual ledger**

- [x] Compact-support surface.
- [x] Centeredness surface.
- [x] Smearing surface.
- [x] Downstream handoff to the observable-atom lane.
- [ ] Keep handoff / receipt objects separated from theorem-body closure.

### G. R6 exact atom `33/20`

Status: **installed as the value-pinning route; review remains source-dependent**

- [x] R5 handoff input for exact atom `33/20`.
- [x] Yang--Mills Hamiltonian spectral-carrier alignment.
- [x] Non-definitional origin certificate.
- [x] R6 normalized spectral/PVM atom route.
- [x] Canonical exact-value theorem: `exact_atom_3320_r6_exact_gap_value_eq_3320_ready`.
- [x] Atom membership for `exactGapValueReal`.
- [ ] Keep documentation clear that this is not pre-R6 definitional unfolding.

### H. R7 positive spectral-weight witness

Status: **installed and terminal-visible**

- [x] Bridge from R6 exact atom to positive spectral weight.
- [x] `massWitness.positiveMass = true` terminal payload.
- [x] Exact value preserved.
- [x] Atom membership preserved.
- [x] Orthogonal non-vacuum witness sector.
- [ ] Keep witness / receipt content classified before public mathematical promotion.

### I. Terminal R1--R7 audit chain

Status: **installed as terminal audit chain; not external acceptance**

- [x] Bundle R1 through R7 into terminal chain.
- [x] Record exact value `33/20` at terminal level.
- [x] Record positive spectral weight at terminal level.
- [x] Carry R4 genuine-PVM law components to the terminal layer.
- [x] Keep final-release hold and public-boundary lock explicit.
- [ ] Keep dependency audit active so that terminal receipts are not treated as a substitute for theorem-body review.

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

### J. Public / external audit receipt surface

Status: **installed as internal audit surface; external review remains active**

- [x] Terminal discharge audit receipt.
- [x] Public audit surface.
- [x] Public audit chain index.
- [x] External audit handoff.
- [x] External audit receipt chain index.
- [x] Projection of exact `33/20` and positive weight from terminal receipt.
- [x] Explicit final-release hold and public-boundary lock.
- [ ] Keep public wording bounded by external review status.

### K. Axiomatic / OS-Wightman / Euclidean construction route

Status: **installed as conditional closure, construction-target bridge, and external-audit projection; not an unconditional construction by itself**

- [x] Axiomatic Yang--Mills mass-gap closure theorem target.
- [x] Axiomatic external audit projection.
- [x] OS/Wightman Hamiltonian reconstruction spine.
- [x] OS/Wightman mass-gap definition bridge.
- [x] OS/Wightman mass-gap external audit bridge.
- [x] Euclidean measure to mass-gap pipeline.
- [x] Euclidean Yang--Mills measure unconditional-construction target surface.
- [x] Finite-volume / continuum construction spine.
- [x] Euclidean construction-spine external audit bridge.
- [x] `ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection`.
- [x] `external_audit_readiness_euclidean_yang_mills_construction_spine_projection`.
- [x] `external_audit_readiness_euclidean_construction_spine_exact_gap_positive`.
- [x] `external_audit_readiness_euclidean_construction_spine_exact_gap_threshold`.
- [x] `external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation`.
- [ ] Keep this lane clearly described as a bridge into which a concrete construction must plug.
- [ ] Review all assumptions, construction fields, and proof-debt markers before public promotion.

```text
MGAP4D/MathlibAnalytic/AxiomaticYangMillsMassGapClosure.lean
MGAP4D/MathlibAnalytic/OSWightmanHamiltonianReconstructionSpine.lean
MGAP4D/MathlibAnalytic/OSWightmanMassGapDefinitionBridge.lean
MGAP4D/MathlibAnalytic/OSWightmanMassGapExternalAuditBridge.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureToMassGapPipeline.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureUnconditionalTarget.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionSpine.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean
docs/axiomatic_yang_mills_mass_gap_closure.md
```

Manual replay for this lane:

```bash
python3 scripts/audit_os_wightman_mass_gap_bridge.py
lake build MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge
```

---

## Active gates

### Gate 1 — Documentation synchronization

Status: **active / repeat after every source-tree change**

- [x] Rewrite `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, and `docs/exact_gap_layer_separation.md` around the current carrier / spectral route / R1--R7 terminal audit surface.
- [x] Add the OS/Wightman and Euclidean construction bridge status to public-facing documentation.
- [x] Add construction-spine external-audit projection status to public-facing documentation.
- [ ] Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and `INDEPENDENT_REPLAY.md` synchronized after each source-tree change.
- [ ] Keep documentation from saying R7 is merely downstream or still absent.
- [ ] Keep documentation from saying exact `33/20` is only a future target.
- [ ] Keep documentation from implying external consensus has completed.
- [ ] Keep documentation from implying construction-spine external-audit projection equals external acceptance.
- [ ] Keep the normalized / dimensional `E0` boundary visible.

### Gate 2 — Placeholder, witness, and proof-debt inventory

Status: **active review layer**

- [ ] Keep `docs/proof_placeholder_inventory.md` synchronized with the source tree.
- [ ] Keep `scripts/audit_proof_placeholder_inventory.py` current.
- [ ] Classify every `StillOpen` marker as active, historical, or explicitly superseded.
- [ ] Classify every `PUnit` and `True` proof-debt marker.
- [ ] Distinguish substantive typed theorem payloads from readiness / witness / receipt records.

Current rule:

```text
PUnit, True, and StillOpen are proof-debt markers unless replaced or explicitly
superseded by typed theorem anchors.
```

### Gate 3 — Fresh-clone replay

Status: **active before any public tag**

- [ ] Run `bash scripts/check.sh` from a fresh clone.
- [ ] Run `lake build`.
- [ ] Record toolchain and replay output.
- [ ] Confirm that audit scripts cover the current OS/Wightman and Euclidean construction bridge files.
- [ ] Confirm `EuclideanYangMillsMeasureConstructionExternalAuditBridge` builds in the reviewed commit.

### Gate 4 — External review packet

Status: **active / not complete**

- [ ] Keep `EXTERNAL_AUDIT_PACKET.md` synchronized with this roadmap.
- [ ] Keep `INDEPENDENT_REPLAY.md` synchronized with this roadmap.
- [ ] Keep final-release hold and public-boundary lock visible.
- [ ] Add review notes append-only.
- [ ] Separate internal replay success from external mathematical acceptance.

### Gate 5 — Version tagging and archive synchronization

Status: **blocked until replay receipt and documentation sync**

- [ ] Create a stable audit tag only after Gate 1--4 are current.
- [ ] Prepare Zenodo / citation metadata after the tag.
- [ ] Do not archive a tag that advertises external consensus or unconditional construction beyond what the Lean bodies support.

---

## Non-goals for the next phase

```text
Do not add another theorem-looking decorative receipt unless it improves reviewability.
Do not move the value 33/20 into Basic.lean or ExactGapReal.lean.
Do not describe the OS/Wightman / Euclidean bridge as an unconditional physical construction by itself.
Do not describe the construction-spine external-audit projection as external acceptance by itself.
Do not treat CI success or audit-script success as external mathematical consensus.
Do not suppress PUnit / True / StillOpen markers from the review surface.
```

---

## Definition of done for the next stable audit tag

A stable audit tag should require:

1. `bash scripts/check.sh` passes from a fresh clone.
2. `lake build` passes under the pinned toolchain.
3. `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `docs/exact_gap_layer_separation.md`, `docs/axiomatic_yang_mills_mass_gap_closure.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and `INDEPENDENT_REPLAY.md` agree.
4. Placeholder inventory is current.
5. The R6/R7/terminal exact-value route is not confused with Basic or ExactGapReal.
6. The OS/Wightman / Euclidean construction route is described as conditional / construction-target material.
7. `ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection` is described as a review-routing projection, not external acceptance.
8. External-consensus and Clay-style acceptance boundaries remain explicit.
