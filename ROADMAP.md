# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open public final theorem release.

---

## Status snapshot as of 2026-05-31

The main branch has advanced beyond the earlier spectral checkpoint into an internal normalized theorem-body / continuum-Hamiltonian / external-audit-readiness surface.

Current normalized theorem-body value:

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
general Fin n / basis / dense-span / operator / spectral boundary: held
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
fresh-clone replay path: present
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

Review principle:

```text
external-audit readiness is not external audit
replay success is not mathematical consensus
CI success is not proof review
documentation is not theorem body
```

---

## Phase A — GitHub-native Lean repository foundation

Status: **complete**

- [x] Initialize Lean 4 Lake project.
- [x] Pin Lean / mathlib lane.
- [x] Establish `MGAP4D.lean` as the top-level import root.
- [x] Establish `MGAP4D/MathlibAnalytic.lean` as the analytic theorem-surface root.
- [x] Add GitHub Actions workflows.
- [x] Add local replay script at `scripts/check.sh`.
- [x] Keep Lean source, docs, ledgers, audit scripts, and CI in one GitHub-native tree.

---

## Phase B — Source migration and structural proof surfaces

Status: **complete**

- [x] Migrate active proof-architecture source files.
- [x] Add OperatorAPI interfaces.
- [x] Add theorem dependency maps as checked Lean structures.
- [x] Add lightweight docs and review maps.
- [x] Archive prior kernels under a reviewed layout.
- [x] Add source-tree review gate.

---

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
spectral checkpoint: internally complete
normalized value surface: 33/20
public final theorem release: not opened
```

---

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

---

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

---

## Phase F — Exact-value origin and audit hardening

Status: **complete as internal audit surface**

- [x] Add exact value theorem-body origin certificate.
- [x] Add major theorem non-placeholder audit script.
- [x] Wire major theorem non-placeholder audit into CI.
- [x] Add bridge coherence audit script.
- [x] Add dedicated bridge-coherence CI workflow.
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

---

## Phase G — Continuum-Hamiltonian route and external-audit readiness

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
- [x] Preserve the boundary before general `Fin n`, basis, dense span, operator, and spectral claims.
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

---

## Phase H — Independent replay and external mathematical review

Status: **active priority**

Purpose: move from internal readiness to externally reproducible review without prematurely converting review success into public final theorem release.

- [ ] Run a fresh-clone replay on at least one second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and complete command transcript.
- [ ] Add `docs/independent_replay_latest.md` as a compact append-only replay receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` command-first and current.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical normalization boundary.
- [ ] Ask at least one reviewer to inspect the continuum-Hamiltonian complete derivation surface.
- [ ] Ask at least one reviewer to inspect the finite-carrier ladder boundary before general `Fin n` promotion.
- [ ] Collect review notes as append-only external audit notes.
- [ ] Preserve the rule: review success does not automatically open public final theorem release.

Exit gate:

```text
fresh-clone replay receipt present
external reviewer transcript present
major theorem-surface review notes present
normalization boundary review notes present
public-boundary wording unchanged
```

---

## Phase I — General finite-carrier ladder hardening

Status: **active but boundary-held**

Purpose: extend the completed `Fin 2` / `Fin 3` Mathlib seed ladder toward a separately reviewed general `Fin n` route.

- [ ] Separate seed examples from general theorem claims.
- [ ] Specify the general `Fin n` target theorem family.
- [ ] Track basis, dense-span, operator, and spectral requirements separately.
- [ ] Add review surfaces before promotion.
- [ ] Add audit hooks that prevent `Fin 2` / `Fin 3` examples from being read as a full general finite-family theorem.
- [ ] Keep public boundary markers visible until the general route is independently reviewed.

Exit gate:

```text
general Fin n route stated
basis / dense-span / operator / spectral obligations separated
seed-to-general promotion blocker visible
audit script prevents accidental overclaim
```

---

## Phase J — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.6-audit`.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Create tag only after source-tree review.
- [ ] Generate post-tag verification receipt.
- [ ] Update Zenodo archive only after the tag and post-tag replay receipt are stable.
- [ ] Keep Zenodo wording clear: proof-architecture and external-audit preparation artifact unless independent consensus changes the boundary.

Exit gate:

```text
tagged commit selected
CI green
fresh-clone replay receipt attached
post-tag verification receipt attached
Zenodo metadata synchronized
public final theorem boundary preserved
```

---

## Phase K — Public communication boundary

Status: **active governance rule**

All public-facing descriptions should preserve the following distinction:

```text
internal normalized Lean theorem-body surface
proof-architecture closure
audit and replay readiness
independent replay
external mathematical consensus
public final theorem acceptance
```

Use:

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
```

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, `PHYSICAL_REALIZATION_BOUNDARY.md`, and CI ledgers synchronized with `main`.
2. Make fresh-clone replay the primary external entry point.
3. Preserve the `33/20` normalized theorem-body origin while keeping the public boundary explicit.
4. Collect independent replay receipts.
5. Harden the continuum-Hamiltonian derivation surface without weakening the external-audit boundary.
6. Advance the finite-carrier ladder from `Fin 2` / `Fin 3` seeds toward a separately reviewed general `Fin n` route.
7. Prepare an audit-oriented version tag only after source-tree review and CI green confirmation.
8. Synchronize Zenodo only after the tag and replay receipt are stable.
9. Continue mathematical hardening while separating proof architecture, replay readiness, and external consensus.

---

## Stop condition

Do not expand the roadmap by adding new phases merely to make the project look larger.

The next public-facing movement should be narrow:

```text
fresh-clone replay
external theorem-surface review
finite-carrier generalization boundary
audit tag
Zenodo synchronization
```

Everything else remains secondary unless it directly supports these gates.
