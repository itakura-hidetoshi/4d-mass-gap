# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface.  KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently supply external mathematical consensus.

---

## Status snapshot as of 2026-06-10

The roadmap has moved beyond the earlier “R7 downstream” framing.

Current `main` should be read as an **internal Lean terminal discharge plus public/external audit receipt surface**, not as a completed external-consensus event.

```text
R1 concrete Hilbert closure: terminal-indexed
R2 infinite-dimensional ℓ² diagonal closed/unbounded operator lane: current main lane
R3 adjoint/self-adjointness theorem discharge: terminal-indexed
R4 genuine-PVM law components: terminal-visible
R5 compact centered plaquette observable: terminal-visible
R6 non-definitional exact atom 33/20: terminal-visible
R7 positive spectral-weight witness: terminal-visible
R1--R7 terminal discharge chain: ready
public/external audit receipt chain: present
external mathematical consensus: not yet claimed
Clay-style public acceptance: not claimed by documentation alone
```

Central Lean-facing payload:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Physical normalization boundary:

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
Delta_phys(E0) = E0 * (33/20)
internal units: E0 = 1, Delta_phys(1) = 33/20
```

Review principle:

```text
Documentation must track theorem bodies.
Do not downgrade completed Lean theorem-body surfaces to open placeholders.
Do not inflate internal Lean discharge into external consensus.
Exact 33/20 is theorem-body visible, not merely a roadmap target.
R7 positive spectral weight is closed inside the terminal chain, not merely downstream.
Proof-debt markers must remain visible until discharged, superseded, or classified as historical.
```

The current short status anchor is:

```text
docs/current_proof_status.md
```

---

## Roadmap posture

The mathematical build-out phase is no longer the main bottleneck.  The next movement is:

```text
synchronization
independent replay
placeholder / witness inventory review
source-tree inspection
external mathematical review
audit-oriented version tagging
Zenodo synchronization
```

Do not add new mathematical phases merely to make the project look larger.  Any new work should directly support review, replay, provenance, or public-boundary accuracy.

---

## Phase A — Repository foundation

Status: **complete**

Completed:

- [x] GitHub-native Lean 4 / Lake repository foundation.
- [x] Pinned Lean / mathlib lane.
- [x] `MGAP4D.lean` top-level root.
- [x] `MGAP4D/MathlibAnalytic.lean` analytic theorem-surface root.
- [x] GitHub Actions workflows.
- [x] `scripts/check.sh` one-command replay path.
- [x] Source migration, theorem dependency maps, review maps, and source-tree review gates.

Exit condition: complete.

---

## Phase B — Normalized exact value and physical-normalization boundary

Status: **complete as normalized theorem-body / carrier boundary**

Completed:

- [x] Add spectral module entrypoint.
- [x] Add spectral gap formalization checkpoint.
- [x] Add exact gap analytic real closure.
- [x] Add Hilbert / Rayleigh / gap-infimum theorem surfaces.
- [x] Record exact normalized theorem-body value `33/20`.
- [x] Add scalar physical-Hamiltonian normalization.
- [x] Add operator physical-Hamiltonian normalization.
- [x] Preserve normalized/dimensional distinction through `E0`.

Current reading:

```text
exactGapValueReal = (33 : ℝ) / 20
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

Boundary retained:

```text
The dimensional physical gap requires a selected positive E0.
External public acceptance is a separate review process.
```

Exit condition: complete; keep documentation synchronized with `PHYSICAL_REALIZATION_BOUNDARY.md`.

---

## Phase C — Exact-gap layer separation

Status: **complete as separation map; active as review discipline**

Purpose: prevent reviewers from confusing carrier definitions, theorem-body payloads, operator/spectral derivation surfaces, and engineering receipts.

Completed:

- [x] Separate the abstract theorem-body layer.
- [x] Separate the normalized carrier layer.
- [x] Separate the operator/spectral derivation layer.
- [x] Separate the engineering / review-marker layer.
- [x] Add current Lean separation map.
- [x] Add human-readable review note.

Anchors:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
docs/exact_gap_layer_separation.md
```

Current reading:

```text
Basic.lean / ExactGapReal.lean = normalized carrier layer
ConcreteR1R7ResidualDischarge.lean = current terminal derivation discharge
ContinuumHamiltonianCompleteMassGapDerivation.lean = complete Hamiltonian spectral derivation surface
YangMillsHamiltonianSpectralDerivation3320.lean = spectral derivation interface into the normalized carrier
ExactGapLayerSeparation.lean = current separation map
```

Exit condition: complete; remain active in external-review instructions.

---

## Phase D — R1--R3 analytic substrate and self-adjointness discharge

Status: **complete in the terminal discharge chain; R2 reading updated**

Purpose: discharge the analytic substrate needed before the genuine PVM / plaquette / atom / weight route.

Completed / terminal-visible:

- [x] R1 concrete real Hilbert substrate closure.
- [x] R2 infinite-dimensional `ℓ²` diagonal closed/unbounded operator lane.
- [x] R2-to-R3 input handoff.
- [x] R2-to-spectral-input handoff.
- [x] R3 adjoint-graph theorem discharge.
- [x] R3 concrete self-adjointness theorem discharge.
- [x] Preserve the distinction between local support lanes and downstream spectral/PVM claims.

Representative anchors:

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean
docs/r2_infinite_l2_diagonal_operator_lane.md
```

Current R2 review route:

```text
ConcreteL2R1HilbertCarrier
  -> ConcreteL2R2DiagonalDomainCandidate
  -> finite-support domain/core
  -> graph-norm finite-support density
  -> graph-norm core release
  -> graph-closedness readiness promotion
  -> graph-closedness obligation promotion
  -> graph-closure closed theorem
  -> completed diagonal graph-defined closed operator
  -> completed Hilbert operator-norm unboundedness
  -> self-adjointness concrete preconditions
  -> R2InfiniteLaneR3InputHandoff
  -> R2InfiniteLaneSpectralInputHandoff
  -> R3 self-adjointness lane
```

Exit condition: complete in terminal R1--R7 discharge chain; keep R2 current-lane wording synchronized.

---

## Phase E — R4 genuine-PVM law components

Status: **complete and terminal-visible, subject to supersession audit for historical markers**

Purpose: move from local finite-supported measurable scaffolds into actual Borel carrier surfaces and genuine-PVM law components usable by R5/R6/R7.

Completed:

- [x] Add actual endpoint carrier from spectral slots into `Set ℝ`.
- [x] Prove empty endpoint realizes `∅`.
- [x] Prove whole endpoint realizes `Set.univ`.
- [x] Prove endpoint measurability.
- [x] Add endpoint complement / union / intersection laws.
- [x] Define actual Borel carrier wrapper `{ s : Set ℝ // MeasurableSet s }`.
- [x] Add wrapper complement / union / intersection operations.
- [x] Lift endpoint slots into the actual Borel wrapper.
- [x] Add explicit closure witnesses.
- [x] Project R4 genuine-PVM law components into R5.
- [x] Carry R4 law components through R6 and R7.
- [x] Keep operator-topology countable-additivity / convergence visible at terminal level.
- [x] Keep no-shell-to-full-collapse boundary visible at terminal level.

Terminal-visible law components:

```text
empty maps to zero
univ maps to identity
pointwise idempotence
intersection/multiplicativity
disjoint-union pointwise additivity
operator-topology countable additivity / convergence theorem
no-shell-to-full-collapse boundary
```

Representative anchors:

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsForR5.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge.lean
docs/r4_terminal_status_supersession.md
```

Exit condition: complete and terminal-visible; historical `StillOpen` markers must remain classified or superseded.

---

## Phase F — R5 compact centered plaquette observable

Status: **complete in the hard-physical-residual ledger**

Purpose: expose the compact centered plaquette observable through theorem-body proof and consume the R4 genuine-PVM handoff.

Completed:

- [x] Add direct decomposition of compact-plaquette review-surface readiness.
- [x] Extract compact support for the R5 chosen observable.
- [x] Extract centeredness for the R5 chosen observable.
- [x] Extract smearing for the R5 chosen observable.
- [x] Package compact / centered / smeared chosen-observable laws.
- [x] Transport the laws to the observable-atom chosen observable.
- [x] Add direct-proof final export.
- [x] Add downstream input contract exposing both chosen-observable faces.
- [x] Discharge the R5 plaquette-observable closure after R4 genuine PVM.

Representative anchors:

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableReviewReadyDirectProof.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofFinalExport.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofDownstreamInputContract.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure.lean
```

Exit condition: complete and consumed by R6.

---

## Phase G — R6 non-definitional exact atom 33/20

Status: **complete and terminal-visible**

Purpose: derive exact atom `33/20` through the observable-atom theorem body and R5 handoff, not through documentation or an isolated carrier definition.

Completed:

- [x] Add R5 handoff input for exact atom `33/20`.
- [x] Add non-definitional origin certificate.
- [x] Prove exact value equality.
- [x] Prove atom membership for `exactGapValueReal`.
- [x] Bridge direct R5 observable review to exact atom lane.
- [x] Discharge R6 non-definitional exact atom closure in the hard-residual ledger.

Key theorem:

```lean
theorem exact_atom_3320_value_eq :
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

Representative anchors:

```text
MGAP4D/R6/Theorem/ExactAtom3320R5Handoff.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
MGAP4D/HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.lean
```

Exit condition: complete and consumed by R7.

---

## Phase H — R7 positive spectral-weight witness

Status: **complete and terminal-visible**

Purpose: close the positive spectral-weight witness after R6 exact atom `33/20`, preserving atom membership and non-vacuum orthogonal-sector placement.

Completed:

- [x] Add R7 bridge from R6 exact atom to positive spectral weight.
- [x] Consume `observableSpectralWeight3320Certificate.ready`.
- [x] Prove `massWitness.positiveMass = true`.
- [x] Preserve exact value `exactGapValueReal = (33 : ℝ) / 20`.
- [x] Preserve atom membership.
- [x] Prove witness sector is orthogonal and not vacuum.
- [x] Close the R7 review slot.
- [x] Discharge R7 positive spectral-weight closure in the hard-residual ledger.

Representative anchors:

```text
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotProjections.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

Key payload:

```lean
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
  observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  witnessSector = orthogonal ∧ witnessSector ≠ vacuum
```

Exit condition: complete and consumed by terminal chain.

---

## Phase I — Terminal R1--R7 discharge chain

Status: **complete / ready**

Purpose: index the full R1--R7 proof-carrying chain and keep exact value, positive spectral weight, R4 countable-additivity receipt, proof-boundary governance, and physical-normalization boundaries visible at the terminal layer.

Completed:

- [x] Bundle R1 concrete Hilbert closure.
- [x] Bundle R2 infinite `ℓ²` diagonal operator closure.
- [x] Bundle R3 theorem/self-adjointness discharge.
- [x] Bundle R4 genuine-PVM closure.
- [x] Bundle R5 plaquette-observable closure.
- [x] Bundle R6 exact atom closure.
- [x] Bundle R7 positive spectral-weight closure.
- [x] Carry R4 law components to R7.
- [x] Record exact value `33/20` at terminal level.
- [x] Record positive spectral weight at terminal level.
- [x] Keep R4 operator-topology countable additivity visible at terminal level.
- [x] Keep final-release hold and public-boundary lock explicit.

Representative anchors:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
```

Key terminal theorem:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Exit condition: complete.

---

## Phase J — Public / external audit receipt surface

Status: **complete as internal audit surface; external review remains active**

Purpose: expose the terminal chain to audit while preserving the distinction between Lean-internal discharge, reproducibility evidence, and external mathematical consensus.

Completed:

- [x] Add terminal discharge audit receipt.
- [x] Add public audit surface.
- [x] Add public audit chain index.
- [x] Add external audit handoff.
- [x] Add external audit receipt chain index.
- [x] Project exact `33/20` and positive weight from terminal receipt.
- [x] Project R4 genuine-PVM law receipts.
- [x] Keep final-release hold explicit.
- [x] Keep public-boundary lock explicit.

Representative anchors:

```text
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

Exit condition: complete as internal/public audit surface; external review remains a separate process.

---

## Phase K — Placeholder, witness, and proof-debt inventory

Status: **active review layer**

Purpose: ensure that theorem bodies, placeholders, witness slots, readiness packets, receipts, and engineering markers are not conflated.

Current tasks:

- [ ] Keep `docs/proof_placeholder_inventory.md` synchronized with the source tree.
- [ ] Keep `scripts/audit_proof_placeholder_inventory.py` current.
- [ ] Classify every `StillOpen` marker as active, historical, or explicitly superseded.
- [ ] Classify every `PUnit` and `True` proof-debt marker.
- [ ] Distinguish substantive typed theorem payloads from readiness/witness/receipt records.
- [ ] Ensure all public-facing documents preserve this distinction.

Current rule:

```text
PUnit, True, and StillOpen are open proof-debt markers unless they are replaced,
discharged, or explicitly superseded by typed theorem anchors.

Provenance and readiness markers remain review-order evidence unless their
payload is a substantive typed theorem.
```

Exit gate:

```text
placeholder inventory updated
source-tree scan attached
active vs historical markers classified
public-boundary wording synchronized
```

---

## Phase L — Independent replay and external mathematical review

Status: **active governance layer**

Purpose: move from internal Lean terminal discharge to externally reproducible review without confusing replay success with public theorem acceptance.

Current tasks:

- [ ] Run a fresh-clone replay on at least one second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and complete command transcript.
- [ ] Add or refresh `docs/independent_replay_latest.md` as a compact append-only replay receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` command-first and current.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `docs/current_proof_status.md`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical-normalization boundary.
- [ ] Ask at least one reviewer to inspect the exact-gap layer separation.
- [ ] Ask at least one reviewer to inspect the placeholder / witness inventory.
- [ ] Ask at least one reviewer to inspect the R2 infinite `ℓ²` lane.
- [ ] Ask at least one reviewer to inspect the R4 genuine-PVM law components.
- [ ] Ask at least one reviewer to inspect the R6 exact atom `33/20` theorem bodies.
- [ ] Ask at least one reviewer to inspect the R7 positive-weight theorem bodies.
- [ ] Ask at least one reviewer to inspect the terminal R1--R7 discharge chain and public/external audit receipt chain.
- [ ] Collect review notes as append-only external audit notes.

Exit gate:

```text
fresh-clone replay receipt present
external reviewer transcript present
R2 lane review notes present
R4 law-component review notes present
R6 exact atom review notes present
R7 positive-weight review notes present
terminal-chain review notes present
placeholder inventory review notes present
physical-normalization review notes present
public-boundary wording synchronized
```

---

## Phase M — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

Purpose: create a stable audit snapshot only after replay, source-tree review, and public-boundary wording are synchronized.

Current tasks:

- [ ] Choose an audit-oriented version name, for example `v1.7-terminal-discharge-audit` or the next appropriate audit tag.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET / current_proof_status consistency.
- [ ] Confirm documentation no longer says R7 is merely downstream.
- [ ] Confirm documentation states exact `33/20` as theorem-body visible.
- [ ] Confirm documentation states positive spectral weight as theorem-body visible.
- [ ] Confirm documentation foregrounds the current R2 infinite `ℓ²` lane.
- [ ] Confirm documentation foregrounds exact-gap layer separation.
- [ ] Confirm documentation foregrounds placeholder / witness inventory.
- [ ] Confirm documentation preserves the distinction between internal Lean terminal discharge and external consensus.
- [ ] Create tag only after source-tree review.
- [ ] Generate post-tag verification receipt.
- [ ] Update Zenodo archive only after the tag and post-tag replay receipt are stable.

Exit gate:

```text
tagged commit selected
CI green
fresh-clone replay receipt attached
post-tag verification receipt attached
Zenodo metadata synchronized
internal terminal discharge accurately described
proof-debt inventory accurately described
external consensus boundary preserved
```

---

## Public communication boundary

Status: **active governance rule**

Use:

```text
MGAP4D currently provides a Lean 4 proof-carrying and replayable audit surface
for a normalized 4D mass-gap route.  The internal terminal R1--R7 discharge
chain carries exact value 33/20 and a positive spectral-weight witness.
External mathematical consensus and Clay-style public acceptance remain separate
review processes.
```

Avoid wording that implies:

```text
R7 is still unproved or merely downstream
exact 33/20 is only a roadmap target
positive spectral weight is still open inside the Lean terminal chain
README/ROADMAP are substitutes for theorem bodies
external peer review has completed
Clay-style public acceptance has completed
dimensional physical gap is fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
readiness receipts are theorem bodies without typed theorem payloads
historical StillOpen markers can be ignored without classification
```

---

## Current priorities

1. Keep README, ROADMAP, `docs/current_proof_status.md`, `THEOREM_INDEX.md`, and `EXTERNAL_AUDIT_PACKET.md` synchronized.
2. Keep the R2 infinite `ℓ²` lane visible as the current main R2 reading.
3. Keep exact-gap layer separation visible to prevent carrier/derivation confusion.
4. Keep placeholder, witness, and proof-debt inventory visible.
5. Add or refresh independent replay receipts.
6. Confirm CI green on the documentation / audit-synchronization commit.
7. Prepare an audit-oriented tag after source-tree review.
8. Synchronize Zenodo metadata after the tag and post-tag replay receipt.
9. Preserve the normalized/dimensional physical-scale boundary.
10. Preserve the distinction between internal Lean terminal discharge and external public acceptance.

---

## Stop condition

Do not expand the roadmap by adding new mathematical phases merely to make the project look larger.

The next movement should be review and synchronization, not another theorem-goal detour:

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
