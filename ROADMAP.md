# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical **MGAP4D Lean proof repository**.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface.  It does not replace this repository as the canonical Lean proof repository and does not independently supply external mathematical consensus.

---

## Status snapshot as of 2026-06-11

Current `main` should be read as an **internal Lean terminal discharge route with a public / external audit receipt surface**.

```text
internal Lean terminal route: present
public / external audit receipt surface: present
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed by documentation alone
```

Central Lean-facing payload:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Current proof spine:

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

The project should not move by adding another decorative theorem phase.  The active work is now review, replay, provenance, and public-boundary precision.

```text
repository / documentation synchronization
fresh-clone independent replay
placeholder / witness / proof-debt inventory review
source-tree inspection
external mathematical review
audit-oriented version tagging
Zenodo synchronization after a stable tag and replay receipt
```

New work should directly support one of these goals.  If a change does not improve replayability, theorem-surface clarity, proof-debt classification, external review, or public-boundary accuracy, it should be deferred.

---

## Completed lanes

### A. Repository foundation

Status: **complete**

- [x] GitHub-native Lean 4 / Lake repository foundation.
- [x] Pinned Lean / mathlib lane.
- [x] `MGAP4D.lean` top-level root.
- [x] `MGAP4D/MathlibAnalytic.lean` analytic theorem-surface root.
- [x] GitHub Actions workflows.
- [x] `scripts/check.sh` one-command replay path.

### B. Normalized exact value and physical boundary

Status: **complete as theorem-route payload and physical-normalization boundary**

- [x] Record exact normalized theorem-body value `33/20` at the theorem-route / terminal surfaces.
- [x] Keep `Basic.lean` free of a real-valued numerical gap carrier.
- [x] Keep `ExactGapReal.lean` as downstream real carrier plus raw route witness, without exporting the final normalized equality theorem.
- [x] Add scalar and operator physical-Hamiltonian normalization.
- [x] Preserve normalized / dimensional distinction through `E0`.

```text
continuum_hamiltonian_derives_exact_mass_gap_value:
  exactGapValueReal = (33 : ℝ) / 20

Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

### C. Exact-gap layer separation

Status: **complete as separation map; active as review discipline**

- [x] Separate abstract theorem-body, Basic-layer marker / downstream real carrier, operator / spectral derivation, and engineering / review-marker layers.
- [x] Add Lean separation map and human-readable review note.
- [x] Keep documentation from implying that `Basic.lean` or a local carrier definition alone is the derivation source.

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
docs/exact_gap_layer_separation.md
```

### D. R1--R3 analytic substrate

Status: **complete in the terminal discharge chain; R2 reading updated**

- [x] R1 concrete Hilbert closure.
- [x] R2 infinite-dimensional `ℓ²` diagonal closed / unbounded operator lane.
- [x] R2-to-R3 input handoff.
- [x] R2-to-spectral-input handoff.
- [x] R3 adjoint / self-adjointness theorem discharge.

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean
docs/r2_infinite_l2_diagonal_operator_lane.md
```

### E. R4 genuine-PVM law components

Status: **complete and terminal-visible, subject to supersession audit for historical markers**

- [x] Actual Borel carrier surface.
- [x] Empty / whole / complement / union / intersection laws.
- [x] Operator-topology countable-additivity / convergence receipt.
- [x] R4 handoff into R5, R6, and R7.

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
docs/r4_terminal_status_supersession.md
```

### F. R5 compact centered plaquette observable

Status: **complete in the hard-physical-residual ledger**

- [x] Compact support.
- [x] Centeredness.
- [x] Smearing.
- [x] Downstream handoff to the observable-atom lane.

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofFinalExport.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure.lean
```

### G. R6 exact atom 33/20

Status: **complete and terminal-visible**

- [x] R5 handoff input for exact atom `33/20`.
- [x] Non-definitional origin certificate.
- [x] Exact value equality at the R6 / theorem-route surface.
- [x] Atom membership for `exactGapValueReal`.

```lean
theorem exact_atom_3320_value_eq :
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

```text
MGAP4D/R6/Theorem/ExactAtom3320R5Handoff.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.lean
```

### H. R7 positive spectral-weight witness

Status: **complete and terminal-visible**

- [x] Bridge from R6 exact atom to positive spectral weight.
- [x] `massWitness.positiveMass = true`.
- [x] Exact value preserved.
- [x] Atom membership preserved.
- [x] Orthogonal non-vacuum witness sector.

```lean
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
  observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  witnessSector = orthogonal ∧ witnessSector ≠ vacuum
```

```text
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

### I. Terminal R1--R7 discharge chain

Status: **complete / ready**

- [x] Bundle R1 through R7 into terminal discharge chain.
- [x] Record exact value `33/20` at terminal level.
- [x] Record positive spectral weight at terminal level.
- [x] Keep final-release hold and public-boundary lock explicit.

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
```

### J. Public / external audit receipt surface

Status: **complete as internal audit surface; external review remains active**

- [x] Terminal discharge audit receipt.
- [x] Public audit surface.
- [x] Public audit chain index.
- [x] External audit handoff.
- [x] External audit receipt chain index.
- [x] Projection of exact `33/20` and positive weight from terminal receipt.

```text
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

---

## Active gates

### Gate 1 — Documentation synchronization

Status: **active**

- [x] Rewrite `README.md` and `ROADMAP.md` around the current R1--R7 terminal / public / external audit receipt surface.
- [x] Keep documentation from implying that `Basic.lean` or a local carrier definition alone derives exact `33/20`.
- [ ] Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized after this documentation pass.
- [ ] Keep documentation from saying R7 is merely downstream.
- [ ] Keep documentation from saying exact `33/20` is only a future target.
- [ ] Keep documentation from implying external consensus has completed.
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
PUnit, True, and StillOpen are open proof-debt markers unless they are replaced,
discharged, or explicitly superseded by typed theorem anchors.
```

### Gate 3 — Independent replay

Status: **active governance layer**

- [ ] Run a fresh-clone replay on at least one second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and complete command transcript.
- [ ] Add or refresh `docs/independent_replay_latest.md` as a compact append-only replay receipt.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.

### Gate 4 — External mathematical review

Status: **active governance layer**

- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `docs/current_proof_status.md`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect `PHYSICAL_REALIZATION_BOUNDARY.md`.
- [ ] Ask at least one reviewer to inspect `docs/exact_gap_layer_separation.md`.
- [ ] Ask at least one reviewer to inspect `docs/proof_placeholder_inventory.md`.
- [ ] Ask at least one reviewer to inspect `docs/r2_infinite_l2_diagonal_operator_lane.md`.
- [ ] Ask at least one reviewer to inspect `docs/r4_terminal_status_supersession.md`.
- [ ] Ask at least one reviewer to inspect the R2, R4, R5, R6, R7, terminal-chain, and public / external audit surfaces.
- [ ] Collect review notes as append-only external audit notes.

### Gate 5 — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.7-terminal-discharge-audit` or the next appropriate audit tag.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm fresh-clone `bash scripts/check.sh` and `lake build`.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET / current_proof_status consistency.
- [ ] Confirm placeholder inventory and exact-gap layer separation are foregrounded.
- [ ] Create tag only after source-tree review.
- [ ] Generate post-tag verification receipt.
- [ ] Update Zenodo only after the tag and post-tag replay receipt are stable.

---

## Public communication boundary

Use:

```text
MGAP4D currently provides a Lean 4 proof-carrying and replayable audit surface
for a normalized 4D mass-gap route. The internal R1--R7 terminal discharge
chain carries exact value 33/20 and a positive spectral-weight witness.
External mathematical consensus and Clay-style public acceptance remain separate
review processes.
```

Do **not** say:

```text
R7 is still unproved or merely downstream
exact 33/20 is only a roadmap target
positive spectral weight is still open inside the Lean terminal chain
README / ROADMAP are substitutes for theorem bodies
external peer review has completed
Clay-style public acceptance has completed
dimensional physical gap is fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
historical StillOpen markers can be ignored without classification
```

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized.
2. Keep the R2 infinite `ℓ²` lane visible as the current main R2 reading.
3. Keep exact-gap layer separation visible to prevent carrier / derivation confusion.
4. Keep placeholder, witness, and proof-debt inventory visible.
5. Add or refresh independent replay receipts.
6. Confirm CI green on the documentation / audit-synchronization commit.
7. Prepare an audit-oriented tag after source-tree review.
8. Synchronize Zenodo metadata after the tag and post-tag replay receipt.
9. Preserve the normalized / dimensional physical-scale boundary.
10. Preserve the distinction between internal Lean terminal discharge and external public acceptance.

---

## Stop condition

Do not expand the roadmap by adding new mathematical phases merely to make the project look larger.

The next movement should be:

```text
README / ROADMAP synchronization
THEOREM_INDEX synchronization
EXTERNAL_AUDIT_PACKET synchronization
current_proof_status synchronization
placeholder / witness inventory review
fresh-clone replay receipt
CI confirmation
version tag
Zenodo synchronization
external mathematical review
```

Everything else remains secondary unless it directly supports these gates.
