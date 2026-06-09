# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently supply external mathematical consensus.

---

## Status snapshot as of 2026-06-09

The roadmap has moved beyond the earlier “R7 downstream” description.

Current state:

```text
R1 concrete Hilbert substrate: complete in the terminal discharge ledger
R2 dense-domain operator closure: complete in the terminal discharge ledger
R3 Mathlib adjoint/self-adjointness theorem discharge: complete in the terminal discharge ledger
R4 genuine-PVM law components: complete and visible at terminal R7 level
R5 compact centered plaquette observable: complete in the terminal discharge chain
R6 non-definitional exact atom 33/20: complete
R7 positive spectral-weight witness: complete
R1--R7 terminal discharge chain: ready
terminal discharge audit receipt: ready
```

Central Lean payload:

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

Repository-governance boundary:

```text
internal Lean terminal discharge: present
exact normalized value 33/20: theorem-body visible
positive spectral-weight witness: theorem-body visible
R4 operator-topology countable-additivity/convergence receipt: terminal-visible
public/external mathematical acceptance: separate review process
Clay-style public acceptance: not claimed by documentation alone
```

Review principle:

```text
Documentation must track theorem bodies.
Do not downgrade completed Lean theorem-body surfaces to open placeholders.
Do not inflate internal Lean discharge into external consensus.
Exact 33/20 is now theorem-body visible, not merely roadmap intent.
R7 positive spectral weight is now closed, not merely downstream.
```

---

## Phase A — Repository foundation

Status: **complete**

- [x] GitHub-native Lean 4 / Lake repository foundation.
- [x] Pinned Lean / mathlib lane.
- [x] `MGAP4D.lean` top-level root.
- [x] `MGAP4D/MathlibAnalytic.lean` analytic theorem-surface root.
- [x] GitHub Actions workflows.
- [x] `scripts/check.sh` one-command replay path.
- [x] Source migration, theorem dependency maps, review maps, and source-tree review gates.

Exit condition: complete.

---

## Phase B — Normalized theorem-body value and physical-normalization boundary

Status: **complete**

Completed:

- [x] Add spectral module entrypoint.
- [x] Add spectral gap formalization checkpoint.
- [x] Add exact gap analytic real closure.
- [x] Add Hilbert Rayleigh quotient theorem surface.
- [x] Add gap infimum / lower-bound / attainment surfaces.
- [x] Record exact normalized theorem-body value `33/20`.
- [x] Add scalar physical-Hamiltonian normalization.
- [x] Add operator physical-Hamiltonian normalization.
- [x] Preserve normalized/dimensional distinction through `E0`.

Current theorem-body reading:

```text
exactGapValueReal = (33 : ℝ) / 20
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

Boundary retained:

```text
dimensional physical gap requires a selected positive E0
external public acceptance is a separate review process
```

---

## Phase C — Continuum-Hamiltonian proof-architecture surfaces

Status: **complete as internal proof-architecture / readiness surfaces**

Completed:

- [x] Add self-adjoint `H_phys` theorem surface.
- [x] Add spectral theorem / PVM / observable surfaces.
- [x] Add compact plaquette and operator-measure compatibility surfaces.
- [x] Add exact gap theorem-body closure.
- [x] Add concrete Hilbert and concrete `H_phys` realization surfaces.
- [x] Add infinite-dimensional Yang-Mills realization target layer.
- [x] Add complete infinite-dimensional Hilbert construction lane.
- [x] Add Hilbert-to-physical unbounded-operator bridge.
- [x] Add self-adjoint `H_phys` lane hardening.
- [x] Add continuum Yang-Mills lane hardening.
- [x] Add plaquette spectral weight lane hardening as a theorem-surface lane.
- [x] Add continuum Hamiltonian theorem and complete derivation surfaces.
- [x] Add internal review residual closure gate.
- [x] Add external audit readiness gate and replay certificate.

Exit condition: complete as internal proof-architecture surface; external review remains separate.

---

## Phase D — R1--R3 analytic substrate and self-adjointness discharge

Status: **complete in the hard-physical-residual ledger**

Purpose: discharge the analytic substrate needed before the genuine PVM / plaquette / atom / weight route.

Completed / terminal-ledger visible:

- [x] R1 concrete real Hilbert substrate closure.
- [x] R2 dense-domain unbounded-operator closure.
- [x] R3 Mathlib adjoint-graph and concrete self-adjointness theorem discharge.
- [x] Preserve the distinction between local support lanes and downstream spectral/PVM claims.

Representative terminal index fields:

```text
r1ConcreteHilbertClosureReady
r2DenseDomainOperatorClosureReady
r3TheoremDischargeReady
```

Exit condition: complete in terminal R1--R7 discharge chain.

---

## Phase E — R4 actual-Borel carrier, wrapper, and genuine-PVM law components

Status: **complete and terminal-visible**

Purpose: move from local finite-supported measurable scaffolds into actual Borel carrier surfaces and then into genuine-PVM law components usable by R5/R6/R7.

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
- [x] Project R4 genuine-PVM law components into the R5 handoff boundary.
- [x] Carry R4 law components through the R6 exact atom bridge.
- [x] Carry R4 law components through the R7 positive-weight bridge.

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

Representative files:

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsForR5.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge.lean
```

Exit condition: complete and terminal-visible.

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

Representative files:

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

Status: **complete**

Purpose: derive exact atom `33/20` through the observable-atom theorem body and R5 handoff, not through documentation or isolated definition.

Completed:

- [x] Add R5 handoff input for exact atom `33/20`.
- [x] Add non-definitional origin certificate.
- [x] Prove exact value equality:

```lean
theorem exact_atom_3320_value_eq :
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

- [x] Prove atom membership for `exactGapValueReal`.
- [x] Bridge direct R5 observable review to exact atom lane.
- [x] Discharge R6 non-definitional exact atom closure in the hard-residual ledger.

Representative files:

```text
MGAP4D/R6/Theorem/ExactAtom3320R5Handoff.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
MGAP4D/HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.lean
```

Exit condition: complete and consumed by R7.

---

## Phase H — R7 positive spectral-weight witness

Status: **complete**

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

Representative files:

```text
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotProjections.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

Exit condition: complete and consumed by terminal chain.

---

## Phase I — Terminal R1--R7 discharge chain

Status: **complete / ready**

Purpose: index the full R1--R7 proof-carrying chain and keep the exact value, positive spectral weight, R4 countable-additivity receipt, and public-boundary governance visible at the terminal layer.

Completed:

- [x] Bundle R1 concrete Hilbert closure.
- [x] Bundle R2 dense-domain operator closure.
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

Representative files:

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

## Phase J — Terminal audit receipt and public audit surface

Status: **complete as internal audit surface; external review remains active**

Purpose: expose the terminal chain to audit while preserving the distinction between Lean-internal discharge and external mathematical consensus.

Completed:

- [x] Add terminal discharge audit receipt.
- [x] Project exact `33/20` and positive weight from terminal receipt.
- [x] Project orthogonal non-vacuum witness from terminal receipt.
- [x] Keep final-release hold explicit.
- [x] Keep public-boundary lock explicit.
- [x] Add public audit surfaces / chain index / external-audit handoff surfaces.

Representative files:

```text
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
```

Exit condition: complete as internal audit surface.

---

## Phase K — Independent replay and external mathematical review

Status: **active governance layer**

Purpose: move from internal Lean terminal discharge to externally reproducible review without confusing review success with public theorem acceptance.

Current tasks:

- [ ] Run a fresh-clone replay on at least one second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and complete command transcript.
- [ ] Add `docs/independent_replay_latest.md` as a compact append-only replay receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` command-first and current.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical-normalization boundary.
- [ ] Ask at least one reviewer to inspect the R4 genuine-PVM law components.
- [ ] Ask at least one reviewer to inspect the R6 exact atom `33/20` theorem bodies.
- [ ] Ask at least one reviewer to inspect the R7 positive-weight theorem bodies.
- [ ] Ask at least one reviewer to inspect the terminal R1--R7 discharge chain and audit receipt.
- [ ] Collect review notes as append-only external audit notes.

Exit gate:

```text
fresh-clone replay receipt present
external reviewer transcript present
R4 law-component review notes present
R6 exact atom review notes present
R7 positive-weight review notes present
terminal-chain review notes present
physical-normalization review notes present
public-boundary wording synchronized
```

---

## Phase L — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.7-terminal-discharge-audit` or the next appropriate audit tag.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Confirm documentation does not say R7 is still downstream.
- [ ] Confirm documentation states exact `33/20` as theorem-body visible.
- [ ] Confirm documentation states positive spectral weight as theorem-body visible.
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
```

---

## Current priorities

1. Keep README and ROADMAP synchronized with the completed R1--R7 terminal discharge chain.
2. Update `THEOREM_INDEX.md` to foreground R6 exact atom `33/20`, R7 positive weight, and terminal discharge receipt.
3. Update external-audit documents so they no longer describe R7 as merely downstream.
4. Add or refresh independent replay receipts.
5. Confirm CI green on the terminal-discharge documentation commit.
6. Prepare an audit-oriented tag after source-tree review.
7. Synchronize Zenodo metadata after the tag and post-tag replay receipt.
8. Preserve the normalized/dimensional physical-scale boundary.
9. Preserve the distinction between internal Lean terminal discharge and external public acceptance.

---

## Stop condition

Do not expand the roadmap by adding new mathematical phases merely to make the project look larger.

The next movement should be review and synchronization, not another theorem-goal detour:

```text
THEOREM_INDEX synchronization
EXTERNAL_AUDIT_PACKET synchronization
fresh-clone replay receipt
CI confirmation
version tag
Zenodo synchronization
external mathematical review
```

Everything else remains secondary unless it directly supports these gates.
