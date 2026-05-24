# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference this repository as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository, and they do not independently open public final theorem release.

## Current status snapshot, 2026-05-25

The `main` branch has advanced beyond the earlier spectral checkpoint into an internal normalized theorem-body / continuum-Hamiltonian / external-audit-readiness surface, and now also contains the Mathlib `ℓ²(ℕ, ℝ)` finite-synthesis carrier API gate plus the R2 dense-domain and graph-submodule frontier lane.

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
Hilbert-to-physical unbounded-operator bridge: present
self-adjoint H_phys lane hardening: present
continuum Yang-Mills lane hardening: present
plaquette spectral-weight lane hardening: present
continuum-Hamiltonian theorem and release surfaces: present
continuum-Hamiltonian complete derivation surfaces: present
finite-carrier Mathlib seed ladder over Fin 2 / Fin 3: present
general Fin n finite-synthesis carrier API gate: present
finite-carrier spectral audit boundary: present
R2 dense-domain release: present
R2 graph-norm core handoff: present
R2 graph-pair transport and explicit linear closure: present
R2 graph-submodule frontier and ambient-law checklist: present
R2 graph-energy pre-surface and finite-prefix terminal: present
R2 graph-norm topology target frontier: present
completed graph-energy / graph-norm candidate / topology construction: active frontier, not final theorem release
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

Review principle:

```text
external-audit readiness is not external audit
replay success is not mathematical consensus
CI success is not proof review
documentation is not theorem body
frontier PR success is not downstream spectral closure
```

## Phase A — GitHub-native Lean repository foundation

Status: **complete**

- [x] Initialize Lean 4 Lake project.
- [x] Pin Lean / mathlib lane.
- [x] Establish `MGAP4D.lean` as the top-level import root.
- [x] Establish `MGAP4D/MathlibAnalytic.lean` as the analytic theorem-surface root.
- [x] Add GitHub Actions workflows.
- [x] Add local replay script at `scripts/check.sh`.
- [x] Keep Lean source, docs, ledgers, audit scripts, and CI in one GitHub-native tree.

## Phase B — Source migration and structural proof surfaces

Status: **complete**

- [x] Migrate active R1--R7 root files.
- [x] Add OperatorAPI interfaces.
- [x] Add R1 / R2 / R3--R7 concrete files.
- [x] Add Global / Concrete status-only files.
- [x] Add theorem dependency map as checked Lean structures.
- [x] Add lightweight docs and maps.
- [x] Archive prior kernels under a reviewed layout.
- [x] Add source-tree review gate.

## Phase C — Spectral checkpoint and exact normalized value

Status: **complete as internal theorem-body surface**

- [x] Add spectral module entrypoint.
- [x] Add spectral gap formalization checkpoint.
- [x] Add exact gap analytic real closure.
- [x] Add Hilbert Rayleigh quotient theorem surface.
- [x] Add gap infimum / lower-bound / attainment surfaces.
- [x] Record exact normalized theorem-body value `33/20`.
- [x] Preserve the distinction between internal normalized value and public final theorem acceptance.

Boundary retained:

```text
spectral checkpoint: complete internally
normalized value surface: 33/20
public final theorem release: not opened
```

## Phase D — Analytic theorem-body and concrete residual closure

Status: **complete as internal proof-architecture surfaces**

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

Internally closed residual surfaces:

```text
concrete Hilbert realization
concrete H_phys / unbounded-operator realization
spectral measure / PVM exact-atom realization
compact lattice-gauge plaquette observable construction
operator-measure realization and compatibility
```

## Phase E — Physical Hamiltonian normalization

Status: **complete as scalar and operator normalization surfaces**

- [x] Add physical Hamiltonian scalar normalization bridge.
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

## Phase F — Exact-value origin and audit hardening

Status: **complete as internal audit surface**

- [x] Add exact value theorem-body origin certificate.
- [x] Add major theorem non-placeholder audit script.
- [x] Wire major theorem non-placeholder audit into CI.
- [x] Add bridge coherence audit script.
- [x] Add dedicated Bridge Coherence CI workflow.
- [x] Check bridge order from Hilbert to physical Hamiltonian to Yang-Mills to spectral/PVM to continuum surfaces.
- [x] Keep public-boundary markers visible.

Audit invariants:

```text
major theorem surfaces do not use sorry/admit/axiom/constant
major theorem surfaces are not trivial True-only statements
33/20 theorem-body origin is checked as a non-placeholder statement
operator-measure/PVM compatibility is checked as a non-placeholder statement
Hamiltonian normalization bridge is checked as a non-placeholder statement
bridge order is mechanically audited
exact value preservation anchors are mechanically audited
public boundary markers are mechanically audited
```

## Phase G — Continuum-Hamiltonian route and external audit readiness

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
- [x] Add finite-carrier Mathlib seed ladder over completed `Fin 2` and `Fin 3` surfaces.
- [x] Add general `Fin n` finite-synthesis carrier templates and API gate.
- [x] Add finite-carrier spectral audit boundary and checklist.
- [x] Add R2 dense-domain release and graph-norm core handoff.
- [x] Add R2 graph-pair transport, explicit graph-pair linear operations, and diagonal-graph closure surfaces.
- [x] Add R2 graph-submodule frontier, explicit linear-closed graph surface, ambient linear-structure frontier, and ambient-law checklist.
- [x] Add R2 graph-energy pre-surface, finite energy-prefix surface, finite prefix laws, and graph-norm topology target frontier.
- [x] Preserve the boundary before graph-norm topology, graph-norm density, graph-norm core, closed-operator, self-adjointness, PVM, spectral atom, and positive spectral weight claims.
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

## Phase H — R2 graph-norm topology and operator bridge hardening

Status: **active frontier**

The current active frontier is no longer only a finite-carrier seed ladder. It is the R2 graph-norm construction lane, starting from the merged R2 dense-domain / graph-submodule / graph-energy-prefix surfaces.

Already available on `main`:

- [x] General `Fin n` synthesis carrier API gate over selected coordinate maps.
- [x] Finite-carrier spectral audit boundary.
- [x] R2 dense-domain release.
- [x] R2 graph-norm core handoff surface.
- [x] R2 graph-pair transport and diagonal graph membership witness extraction.
- [x] Explicit graph-pair zero/add/smul operations and compatibility laws.
- [x] Diagonal graph zero/add/smul closure under explicit operations.
- [x] R2 graph-submodule frontier surface.
- [x] Explicit linear-closed graph surface.
- [x] Ambient linear-structure frontier and law checklist.
- [x] Graph-energy pre-surface.
- [x] Finite graph-energy prefix surface and terminal prefix laws.
- [x] Graph-norm topology target frontier.

Active / next R2 obligations:

- [ ] Merge the clean completed graph-energy / graph-norm-candidate frontier PR after CI review.
- [ ] Complete `completed graph energy = ∑' n, energyTerm(p,n)` surface on main.
- [ ] Complete graph-norm candidate `sqrt(completed graph energy)` surface on main.
- [ ] Close candidate nonnegativity, zero law, square law, and absolute homogeneity surfaces on main.
- [ ] Close completed-energy add bound and sqrt-form candidate add-bound on main.
- [ ] Prove the exact graph-norm triangle inequality.
- [ ] Define graph-norm distance candidate and prove self-zero, symmetry, and triangle laws.
- [ ] Construct a named `PseudoMetricSpace` / topology surface without prematurely installing a global instance.
- [ ] Separate topology construction from graph-norm density.
- [ ] Prove graph-norm density / graph-norm core theorem only after the topology surface is stable.
- [ ] Build mathlib `Submodule` packaging for the diagonal graph only after the ambient typeclass law bridge is stable.
- [ ] Route from graph-norm core to the closed-operator theorem as a separate reviewed phase.
- [ ] Route from closed operator to self-adjointness as a separate reviewed phase.
- [ ] Route from self-adjointness to PVM / spectral atom / positive spectral weight as a separate reviewed phase.

Boundary retained:

```text
completed graph-energy frontier is not graph-norm density
graph-norm topology is not graph-norm core
graph-norm core is not closed operator
closed operator is not self-adjointness
self-adjointness is not PVM construction
PVM construction is not spectral atom theorem
spectral atom theorem is not positive spectral weight theorem
frontier PR success is not public final theorem acceptance
```

## Phase I — Independent replay and external mathematical review

Status: **active priority**

- [ ] Run a fresh-clone independent replay on a second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and full command transcript.
- [ ] Add a compact `docs/independent_replay_latest.md` receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` short, current, and command-first.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect the major theorem surfaces in `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical normalization boundary.
- [ ] Ask at least one reviewer to inspect the continuum-Hamiltonian complete derivation surface.
- [ ] Ask at least one reviewer to inspect the finite-carrier / R2 graph-norm frontier boundary.
- [ ] Collect review notes as append-only external audit notes.
- [ ] Do not convert review success into public final theorem release automatically.

## Phase J — Version tag, Zenodo synchronization, and audit release packet

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.0-audit`, `v1.6-audit`, or a later `v1.7-r2-audit` once the R2 graph-norm frontier stabilizes.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Confirm that the R2 frontier wording does not imply downstream closed-operator or spectral claims.
- [ ] Create tag only after source-tree review.
- [ ] Generate post-tag verification receipt.
- [ ] Update Zenodo archive only after the tag and post-tag replay receipt are stable.
- [ ] Keep the Zenodo description clear that the record is a proof-architecture and external-audit preparation artifact unless and until independent consensus changes the boundary.

## Phase K — Public communication boundary

Status: **active governance rule**

All public-facing descriptions should preserve the following distinction:

```text
internal normalized Lean theorem-body surface
proof-architecture closure
audit and replay readiness
R2 graph-norm frontier hardening
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
finite-carrier seeds imply the full general finite-family / spectral theorem chain
R2 graph-submodule frontier equals graph-norm topology
R2 graph-norm topology equals graph-norm core
R2 graph-norm core equals closed-operator theorem
closed operator equals self-adjointness / PVM / spectral atom / positive spectral weight
```

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, and CI ledgers synchronized with `main`.
2. Make fresh-clone replay the primary external entry point.
3. Preserve the `33/20` normalized theorem-body origin while keeping the public boundary explicit.
4. Finish the R2 completed graph-energy / graph-norm-candidate frontier cleanly, without promoting downstream claims.
5. Close graph-norm triangle and pseudo-metric/topology construction as separately reviewable PRs.
6. Keep graph-norm density / core theorem separate from topology construction.
7. Collect independent replay receipts.
8. Harden the continuum-Hamiltonian derivation surface without weakening the external-audit boundary.
9. Prepare an audit-oriented version tag only after source-tree review and CI green confirmation.
10. Synchronize Zenodo only after the tag and replay receipt are stable.
11. Continue mathematical hardening while separating proof architecture, replay readiness, frontier closure, and external consensus.
