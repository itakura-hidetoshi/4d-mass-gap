# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical **MGAP4D Lean proof repository**.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. It does not replace this repository as the canonical Lean proof repository and does not independently supply external mathematical consensus.

---

## Status snapshot as of 2026-06-11

Current `main` should be read as an **internal Lean replay / terminal-audit surface** for a normalized 4D mass-gap route.

```text
internal Lean terminal route: present
public / external audit receipt surface: present
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed by documentation alone
complete public solution of the 4D Yang--Mills mass-gap problem: not claimed
```

Central terminal-audit payload:

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
  -> no exactGapValueReal_eq theorem
  -> no exposed exactGapValueReal = 33/20 equality

Continuum Hamiltonian / PVM / spectral route
  -> aligns exactGapValueReal with a derived Hamiltonian spectral value
  -> carries positivity / nonzero spectral-mass surfaces
  -> keeps final-value adoption gated before R6

R6
  -> non-definitional exact-atom / spectral-PVM value-pinning route for 33/20

R7
  -> positive spectral-weight witness and preservation of exact value

R1--R7 terminal chain
  -> terminal audit projection of exact 33/20 plus positive spectral weight
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

The project should not move by adding another decorative theorem phase. The active work is now:

```text
repository / documentation synchronization
fresh-clone independent replay
placeholder / witness / proof-debt inventory review
source-tree inspection
external mathematical review
audit-oriented version tagging
Zenodo synchronization after a stable tag and replay receipt
```

New work should directly support one of these goals. If a change does not improve replayability, theorem-surface clarity, proof-debt classification, exact-gap layer separation, external review, or public-boundary accuracy, it should be deferred.

---

## Completed or currently installed lanes

The following lanes are installed in the source tree. Their review status must still be read through `docs/proof_placeholder_inventory.md`, because a lane can be present and replayable while still containing receipt, witness, `True`, `PUnit`, or `StillOpen` proof-debt markers.

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
- [x] Keep the Hamiltonian / PVM / spectral route separate from the carrier layer.
- [x] Preserve the normalized / dimensional distinction through `E0`.

```text
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

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

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
docs/r4_terminal_status_supersession.md
```

### F. R5 compact centered plaquette observable

Status: **installed in the hard-physical-residual ledger**

- [x] Compact-support surface.
- [x] Centeredness surface.
- [x] Smearing surface.
- [x] Downstream handoff to the observable-atom lane.
- [ ] Keep handoff / receipt objects separated from theorem-body closure.

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofFinalExport.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure.lean
```

### G. R6 exact atom `33/20`

Status: **installed as the value-pinning route; review remains source-dependent**

- [x] R5 handoff input for exact atom `33/20`.
- [x] Yang--Mills Hamiltonian spectral-carrier alignment.
- [x] Non-definitional origin certificate.
- [x] R6 normalized spectral/PVM atom route.
- [x] Exact value theorem available through the R6 value-pinning hypothesis.
- [x] Atom membership for `exactGapValueReal`.
- [ ] Keep documentation clear that this is not pre-R6 definitional unfolding.

```text
MGAP4D/R6/Theorem/ExactAtom3320R5Handoff.lean
MGAP4D/R6/Theorem/ExactAtom3320YangMillsSpectralDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.lean
```

### H. R7 positive spectral-weight witness

Status: **installed and terminal-visible**

- [x] Bridge from R6 exact atom to positive spectral weight.
- [x] `massWitness.positiveMass = true` terminal payload.
- [x] Exact value preserved.
- [x] Atom membership preserved.
- [x] Orthogonal non-vacuum witness sector.
- [ ] Keep witness / receipt content classified before public mathematical promotion.

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

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
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

```text
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

---

## Active gates

### Gate 1 — Documentation synchronization

Status: **active / repeat after every source-tree change**

- [x] Rewrite `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, and `docs/exact_gap_layer_separation.md` around the current carrier / spectral route / R1--R7 terminal audit surface.
- [x] Correct the Basic-layer reading: marker-only, no real-valued gap carrier.
- [x] Correct the carrier reading: `exactGapValueReal` is the downstream abstract normalized real carrier; its layer proves positivity and above-one facts only.
- [x] Correct the review reading: final public review goes through R1--R7 plus the continuum-Hamiltonian / PVM / spectral route, not through `Basic.lean` or `ExactGapReal.lean` alone.
- [ ] Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized after each source-tree change.
- [ ] Keep documentation from saying R7 is merely downstream or still absent.
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

### Gate 4 — Source-tree reduction and proof-debt closure

Status: **active proof-review layer**

- [ ] Replace every public-route `PUnit` placeholder with a typed mathematical object or explicitly keep it outside theorem closure.
- [ ] Replace every analytic-claim `True` marker with a substantive theorem field or classify it as metadata only.
- [ ] Classify every `StillOpen` marker as active, historical, or superseded by a cited theorem.
- [ ] Distinguish actual Mathlib property theorems from receipts, packets, manifests, and witness-only slots.
- [ ] Re-run the placeholder inventory after each source-tree change.

### Gate 5 — External mathematical review

Status: **active governance layer**

- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `docs/current_proof_status.md`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect `PHYSICAL_REALIZATION_BOUNDARY.md`.
- [ ] Ask at least one reviewer to inspect `docs/exact_gap_layer_separation.md`.
- [ ] Ask at least one reviewer to inspect `docs/proof_placeholder_inventory.md`.
- [ ] Ask at least one reviewer to inspect `docs/r2_infinite_l2_diagonal_operator_lane.md`.
- [ ] Ask at least one reviewer to inspect `docs/r4_terminal_status_supersession.md`.
- [ ] Ask at least one reviewer to inspect the Basic / ExactGapReal / Yang--Mills spectral derivation / R6 / R7 layer separation.
- [ ] Ask at least one reviewer to inspect the terminal-chain and public / external audit surfaces.
- [ ] Collect review notes as append-only external audit notes.

### Gate 6 — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.7-terminal-audit-boundary` or the next appropriate audit tag.
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
for a normalized 4D mass-gap route. The internal R1--R7 terminal chain records
exact value 33/20 and a positive spectral-weight witness. External mathematical
consensus and Clay-style public acceptance remain separate review processes.
```

Do **not** say:

```text
R7 is still unproved or absent
exact 33/20 is only a roadmap target
positive spectral weight is still open inside the Lean terminal chain
Basic.lean itself carries the real-valued numerical gap
ExactGapReal.lean itself proves exactGapValueReal = 33/20
carrier-level arithmetic normalization alone is the physical derivation
README / ROADMAP are substitutes for theorem bodies
external peer review has completed
Clay-style public acceptance has completed
dimensional physical gap is fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
historical StillOpen markers can be ignored without classification
PUnit or True can close an analytic theorem by themselves
```

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized.
2. Keep the Basic / ExactGapReal / spectral-derivation / R6-R7 layer separation visible.
3. Keep the R2 infinite `ℓ²` lane visible as the current main R2 reading.
4. Keep placeholder, witness, and proof-debt inventory visible.
5. Resolve or explicitly supersede `PUnit`, `True`, and `StillOpen` markers before public theorem promotion.
6. Add or refresh independent replay receipts.
7. Confirm CI green on the documentation / audit-synchronization commit.
8. Prepare an audit-oriented tag after source-tree review.
9. Synchronize Zenodo metadata after the tag and post-tag replay receipt.
10. Preserve the normalized / dimensional physical-scale boundary.
11. Preserve the distinction between internal Lean terminal audit chain and external public acceptance.

---

## Stop condition

Do not expand the roadmap by adding new mathematical phases merely to make the project look larger.

The next movement should be:

```text
README / ROADMAP synchronization
THEOREM_INDEX synchronization
EXTERNAL_AUDIT_PACKET synchronization
current_proof_status synchronization
exact_gap_layer_separation synchronization
placeholder / witness inventory review
fresh-clone replay receipt
CI confirmation
source-tree proof-debt reduction
version tag
Zenodo synchronization
external mathematical review
```

Everything else remains secondary unless it directly supports these gates.
