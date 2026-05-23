# MGAP4D Roadmap

This roadmap summarizes the current MGAP4D development state and the next review-gated steps for the canonical Lean proof repository:

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference this repository as a physics-facing bridge and public-core governance surface, but KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open public final theorem release.

## Current status snapshot

The main branch has advanced beyond the earlier spectral checkpoint into an internal normalized theorem-body / continuum-Hamiltonian / external-audit-readiness surface.

Current theorem-body value:

```text
exactGapValueReal = 33 / 20
Delta_norm = 33/20
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

Current repository boundary:

```text
internal normalized theorem-body surface: present
physical Hamiltonian scalar normalization: present
physical Hamiltonian operator normalization: present
complete infinite-dimensional Hilbert construction lane: present
continuum-Hamiltonian theorem and release surfaces: present
continuum-Hamiltonian complete derivation surfaces: present
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

## Phase 1 — GitHub-native project setup

Status: **complete**

- [x] Initialize Lean 4 Lake project.
- [x] Add GitHub Actions using direct `elan`.
- [x] Add audit scripts.
- [x] Add active Lean scaffold.
- [x] Establish `MGAP4D.lean` as top-level import root.
- [x] Establish `MGAP4D/MathlibAnalytic.lean` as analytic theorem-surface root.

## Phase 2 — Source migration and repository layout

Status: **complete**

- [x] Migrate active R1--R7 root files.
- [x] Add lightweight docs and maps.
- [x] Add snapshot root manifests.
- [x] Add Global / Concrete status-only files.
- [x] Add OperatorAPI interfaces.
- [x] Add R1 / R2 / R3--R7 concrete files.
- [x] Archive prior kernels under a reviewed layout.
- [x] Keep the repository GitHub-native: Lean source, docs, ledgers, audit scripts, and CI live in one source tree.

## Phase 3 — Proof hardening and spectral checkpoint

Status: **complete**

- [x] Add theorem-surface layers for OperatorAPI, R1--R7, and Global routes.
- [x] Add theorem dependency map as checked Lean structures.
- [x] Complete replacement passes and closure checkpoints.
- [x] Add Mathlib adoption gate and request registry.
- [x] Complete scoped Mathlib dry-run series.
- [x] Record the main-adoption policy as review-gated.
- [x] Add source-tree review gate.
- [x] Add independent replay preparation.
- [x] Add spectral module entrypoint.
- [x] Add spectral gap formalization checkpoint.
- [x] Wire spectral formalization into the release-gate root.
- [x] Add KuuOS reference bridge.

Boundary retained:

```text
spectral checkpoint: complete internally
public final theorem release: not opened
Mathlib main adoption: explicit proposal / review-gate only
```

## Phase 4 — Release hygiene and external-audit surfaces

Status: **mostly complete; tag/release remains review-gated**

- [x] Move release provenance into `docs/archive/`.
- [x] Keep root README as the GitHub-native entry point.
- [x] Keep public theorem claims review-gated.
- [x] Prepare version-tag readiness notes without creating a tag.
- [x] Prepare source-tree review refresh without creating a tag.
- [x] Add bounded tag creation script without creating a tag.
- [x] Add post-tag verification receipt template.
- [x] Add tag creation tracking issue receipt.
- [x] Add external audit note template without changing active proof semantics.
- [ ] Create a version tag only after CI green confirmation, source-tree review, and boundary review.
- [ ] Add external audit notes without changing active proof semantics.

## Phase 5 — Analytic theorem-body and concrete residual closure

Status: **complete as internal theorem-body / proof-architecture surfaces**

- [x] Add exact gap analytic real closure.
- [x] Add Hilbert Rayleigh quotient theorem surface.
- [x] Add self-adjoint `H_phys` theorem surface.
- [x] Add spectral theorem theorem surface.
- [x] Add PVM theorem surface.
- [x] Add observable atom theorem surface.
- [x] Add compact plaquette construction theorem surface.
- [x] Add operator-measure compatibility theorem surface.
- [x] Add exact gap theorem-body closure.
- [x] Add concrete Hilbert realization theorem.
- [x] Add concrete `H_phys` realization theorem.
- [x] Add physical unbounded-operator skeleton.
- [x] Add concrete Yang-Mills Hamiltonian skeleton.
- [x] Add spectral realization and continuum spectral theorem skeletons.
- [x] Add final theorem release skeleton / closure / chain index / bundle manifest.
- [x] Add concrete residual closure.
- [x] Record concrete residual closure CI in the ledger.

Internally closed residual surfaces:

```text
concrete Hilbert realization
concrete H_phys / unbounded-operator realization
spectral measure / PVM exact-atom realization
compact lattice-gauge plaquette observable construction
operator-measure realization and compatibility
```

Key ledgers:

```text
docs/mathlib_concrete_residual_closure.md
docs/mathlib_concrete_residual_closure_ci.md
docs/mathlib_final_theorem_release_bundle_manifest.md
docs/mathlib_final_theorem_release_bundle_manifest_ci.md
docs/mathlib_final_theorem_release_chain_index.md
docs/mathlib_final_theorem_release_chain_index_ci.md
```

## Phase 6 — Physical Hamiltonian normalization

Status: **complete as scalar and operator normalization surfaces**

- [x] Add physical Hamiltonian scalar normalization bridge.
- [x] Record physical Hamiltonian scalar normalization CI.
- [x] Add physical Hamiltonian operator normalization surface.
- [x] Record operator-normalization CI checkpoint.
- [x] Keep dimensional physical interpretation explicitly dependent on `E0`.
- [x] Preserve public-boundary markers.

Normalization invariant:

```text
reference energy scale E0 is explicit and positive
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
internal normalized units set E0 = 1
dimensionless exact gap is 33/20
dimensional physical gap reads as E0 * 33/20
```

## Phase 7 — Exact-value origin and audit hardening

Status: **complete as internal audit surface**

- [x] Add exact value theorem-body origin certificate.
- [x] Record exact value theorem-body origin CI.
- [x] Add major theorem non-placeholder audit script.
- [x] Wire major theorem non-placeholder audit into CI.
- [x] Add bridge coherence audit script.
- [x] Add dedicated Bridge Coherence CI workflow.
- [x] Record bridge coherence CI in the ledger.
- [x] Ensure public-boundary markers remain visible.

Audit invariants:

```text
major theorem surfaces do not use sorry/admit/axiom/constant
major theorem surfaces are not trivial True-only statements
33/20 theorem-body origin is checked as a non-placeholder statement
operator-measure/PVM compatibility is checked as a non-placeholder statement
Hamiltonian normalization bridge is checked as a non-placeholder statement
Hilbert -> H_phys -> Yang-Mills -> spectral/PVM -> continuum bridge order is mechanically audited
exact value preservation anchors are mechanically audited
public boundary markers are mechanically audited
```

Key ledgers:

```text
docs/mathlib_major_theorem_nonplaceholder_audit.md
docs/mathlib_major_theorem_nonplaceholder_audit_ci.md
docs/mathlib_bridge_coherence_audit.md
docs/mathlib_bridge_coherence_ci.md
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
```

## Phase 8 — Continuum-Hamiltonian route and external audit readiness

Status: **complete as internal readiness gate; external audit still pending**

- [x] Add infinite-dimensional Yang-Mills realization target layer.
- [x] Add infinite-dimensional residual filling bridge.
- [x] Add hard physical residual hardening map.
- [x] Add complete infinite-dimensional Hilbert construction.
- [x] Add Hilbert-to-physical unbounded-operator bridge.
- [x] Add self-adjoint `H_phys` bridge adoption.
- [x] Add self-adjoint `H_phys` lane hardening.
- [x] Add continuum Yang-Mills lane hardening.
- [x] Add plaquette spectral weight lane hardening.
- [x] Add continuum Hamiltonian mass-gap witness hardening.
- [x] Add continuum Hamiltonian mass-gap theorem.
- [x] Add continuum Hamiltonian mass-gap release adoption.
- [x] Add continuum Hamiltonian complete mass-gap derivation.
- [x] Add continuum Hamiltonian complete mass-gap release adoption.
- [x] Add four-lane residual closure.
- [x] Add internal review residual closure gate.
- [x] Add external audit readiness gate.
- [x] Add external audit readiness field classification.
- [x] Add external audit readiness replay certificate.
- [x] Include these stages in `bash scripts/check.sh`.

Current replay path includes:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit physical Hamiltonian operator normalization
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit complete infinite-dimensional Hilbert construction
[check] audit self-adjoint HPhys lane hardening
[check] audit continuum Yang-Mills lane hardening
[check] audit plaquette spectral weight lane hardening
[check] audit continuum Hamiltonian witness hardening
[check] audit four-lane residual closure
[check] audit internal review residual closure gate
[check] audit external audit readiness gate
[check] audit external audit readiness gate field classification
[check] audit external audit readiness replay certificate
[check] replay summary
[check] lake update
[check] build physical Hamiltonian operator normalization
[check] build continuum Hamiltonian exact mass-gap derivation
[check] build continuum Hamiltonian release-chain addendum
[check] build external audit readiness gate
[check] lake build
```

## Phase 9 — Independent replay and external review

Status: **active priority**

- [ ] Run a fresh-clone independent replay on a second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and full command transcript.
- [ ] Add a compact `docs/independent_replay_latest.md` receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` short, current, and command-first.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect the major theorem surfaces in `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical normalization boundary.
- [ ] Collect review notes as append-only external audit notes.
- [ ] Do not convert review success into public final theorem release automatically.

Review principle:

```text
external-audit readiness is not external audit
replay success is not mathematical consensus
CI success is not proof review
documentation is not theorem body
```

## Phase 10 — Version tag, Zenodo synchronization, and release packet

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.0-audit` or `v1.6-audit`.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Create tag only after source-tree review.
- [ ] Generate post-tag verification receipt.
- [ ] Update Zenodo archive only after the tag and post-tag replay receipt are stable.
- [ ] Keep the Zenodo description clear that the record is a proof-architecture and external-audit preparation artifact unless and until independent consensus changes the boundary.

## Phase 11 — Public communication boundary

Status: **active governance rule**

All public-facing descriptions should preserve the following distinction:

```text
internal normalized Lean theorem-body surface
proof-architecture closure
audit and replay readiness
external mathematical consensus
public final theorem acceptance
```

Recommended wording:

```text
MGAP4D currently provides a Lean 4 proof architecture and replayable audit surface
for an internal normalized 4D mass gap theorem-body route with normalized value 33/20.
The repository is prepared for independent replay and external review.
Public final theorem acceptance is not claimed.
```

Avoid wording that implies:

```text
Clay problem officially solved
external peer review completed
dimensional physical gap fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
external-audit-readiness gate equals external audit
```

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and CI ledgers synchronized with `main`.
2. Make fresh-clone replay the primary external entry point.
3. Preserve the `33/20` normalized theorem-body origin while keeping the public boundary explicit.
4. Collect independent replay receipts.
5. Prepare an audit-oriented version tag only after source-tree review and CI green confirmation.
6. Synchronize Zenodo only after the tag and replay receipt are stable.
7. Continue mathematical hardening without weakening the external-audit boundary.
