# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open public final theorem release.

---

## Status snapshot as of 2026-06-01

The main branch has advanced beyond the earlier spectral checkpoint into an internal normalized theorem-body / continuum-Hamiltonian / external-audit-readiness surface, with an additional concrete `l2` R2 local analytic hardening lane.

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
continuum-Hamiltonian complete derivation surfaces: present
finite-carrier Mathlib seed ladder over Fin 2 / Fin 3: present
general Fin n / basis / dense-span / operator / spectral boundary: held
concrete l2 R2 graph-norm core blocker: closed at the current route layer
concrete l2 R2 residual-zero audit surface: present
formal-adjoint graph / operator-value surface for the concrete l2 R2 diagonal model: present
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

Review principle:

```text
external-audit readiness is not external audit
replay success is not mathematical consensus
CI success is not proof review
documentation is not theorem body
formal-adjoint graph equality is not Mathlib IsSelfAdjoint promotion
residual-zero audit is not spectral/PVM/physical-Hamiltonian release
```

---

## Completed foundation phases

Status: **complete**

- [x] GitHub-native Lean 4 / Lake repository foundation.
- [x] Pinned Lean / mathlib lane.
- [x] `MGAP4D.lean` top-level root.
- [x] `MGAP4D/MathlibAnalytic.lean` analytic theorem-surface root.
- [x] GitHub Actions workflows.
- [x] `scripts/check.sh` one-command replay path.
- [x] Source migration, theorem dependency maps, review maps, and source-tree review gates.

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

## Phase D — Analytic theorem-body, physical normalization, and continuum route

Status: **complete as internal proof-architecture / readiness surfaces**

- [x] Add self-adjoint `H_phys` theorem surface.
- [x] Add spectral theorem / PVM / observable surfaces.
- [x] Add compact plaquette and operator-measure compatibility surfaces.
- [x] Add exact gap theorem-body closure.
- [x] Add concrete Hilbert and concrete `H_phys` realization surfaces.
- [x] Add scalar and operator physical Hamiltonian normalization.
- [x] Add infinite-dimensional Yang-Mills realization target layer.
- [x] Add complete infinite-dimensional Hilbert construction lane.
- [x] Add Hilbert-to-physical unbounded-operator bridge.
- [x] Add self-adjoint `H_phys` lane hardening.
- [x] Add continuum Yang-Mills lane hardening.
- [x] Add plaquette spectral weight lane hardening.
- [x] Add continuum Hamiltonian theorem and complete derivation surfaces.
- [x] Add finite-carrier Mathlib seed ladder over `Fin 2` and `Fin 3`.
- [x] Add four-lane residual closure.
- [x] Add internal review residual closure gate.
- [x] Add external audit readiness gate and replay certificate.

---

## Phase E — Independent replay and external mathematical review

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
- [ ] Ask at least one reviewer to inspect the concrete `l2` R2 route without promoting local audit surfaces to global spectral/PVM claims.
- [ ] Collect review notes as append-only external audit notes.
- [ ] Preserve the rule: review success does not automatically open public final theorem release.

Exit gate:

```text
fresh-clone replay receipt present
external reviewer transcript present
major theorem-surface review notes present
normalization boundary review notes present
continuum-Hamiltonian review notes present
concrete l2 R2 boundary review notes present
public-boundary wording unchanged
```

---

## Phase F — Concrete l2 R2 local analytic hardening

Status: **active, boundary-held**

Purpose: use the concrete `l2` R2 diagonal model as a narrow Mathlib-facing analytic lane, while preventing accidental promotion from graph/audit surfaces to operator/spectral/physical claims.

Completed on `main`:

- [x] Add the narrow current-route umbrella.
- [x] Close the old R2f graph-norm core blocker at the current route layer.
- [x] Add the residual-zero audit surface.
- [x] Document `R2_CURRENT_ROUTE.md` after residual-zero audit addition.
- [x] Add formal-adjoint graph candidate structure.
- [x] Add formal-adjoint operator-value surface.
- [x] Prove the formal-adjoint operator-value coordinate equation.
- [x] Prove graph-level equality between the completed diagonal graph carrier and the formal-adjoint graph candidate.

Active / next:

- [ ] Keep residual taxonomy as a separate review lane until merged.
- [ ] Add an explicit boundary audit preventing residual-zero language from implying closed operator / self-adjoint / spectral / PVM / atom / weight / physical-Hamiltonian claims.
- [ ] Decide whether the next narrow promotion target is a closed graph theorem or a Mathlib-compatible densely-defined operator theorem.
- [ ] If attempting a Mathlib `IsSelfAdjoint` promotion, introduce it only as a separate theorem target with all required domain and closed-operator obligations visible.
- [ ] Add review notes explaining why graph-level formal-adjoint equality is not itself a self-adjointness theorem.

Exit gate:

```text
R2 taxonomy merged or explicitly deferred
closed-operator obligations listed
Mathlib self-adjointness obligations listed
spectral/PVM/atom/weight/physical-Hamiltonian nonpromotion audit present
reviewer can distinguish graph equality, closed operator, self-adjointness, spectral theorem, and physical realization
```

---

## Phase G — General finite-carrier ladder hardening

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

## Phase H — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.6-audit`.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Confirm concrete `l2` R2 route wording does not overclaim.
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
R2 local analytic boundary preserved
```

---

## Public communication boundary

Status: **active governance rule**

Use:

```text
MGAP4D currently provides a Lean 4 proof architecture and replayable audit surface
for an internal normalized 4D mass-gap theorem-body route with normalized value 33/20.
The repository is prepared for independent replay and external review.
Public final theorem acceptance is not claimed.
```

Avoid wording that implies:

```text
external peer review completed
dimensional physical gap fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
external-audit-readiness gate equals external audit
finite-carrier seeds imply the full general finite-family / spectral theorem chain
concrete l2 R2 residual-zero audit implies a closed operator theorem
formal-adjoint graph equality implies Mathlib self-adjointness
local R2 analytic surfaces imply PVM / exact atom / positive spectral weight / physical Hamiltonian promotion
```

---

## Current priorities

1. Keep `README.md`, `ROADMAP.md`, `THEOREM_INDEX.md`, `EXTERNAL_AUDIT_PACKET.md`, `PHYSICAL_REALIZATION_BOUNDARY.md`, `docs/R2_CURRENT_ROUTE.md`, and CI ledgers synchronized with `main`.
2. Make fresh-clone replay the primary external entry point.
3. Preserve the `33/20` normalized theorem-body origin while keeping the public boundary explicit.
4. Collect independent replay receipts.
5. Harden the continuum-Hamiltonian derivation surface without weakening the external-audit boundary.
6. Keep the concrete `l2` R2 lane useful but narrow.
7. Advance the finite-carrier ladder from `Fin 2` / `Fin 3` seeds toward a separately reviewed general `Fin n` route.
8. Prepare an audit-oriented version tag only after source-tree review and CI green confirmation.
9. Synchronize Zenodo only after the tag and replay receipt are stable.
10. Continue mathematical hardening while separating proof architecture, replay readiness, and external consensus.

---

## Stop condition

Do not expand the roadmap by adding new phases merely to make the project look larger.

The next public-facing movement should be narrow:

```text
fresh-clone replay
external theorem-surface review
concrete l2 R2 local analytic boundary review
finite-carrier generalization boundary
audit tag
Zenodo synchronization
```

Everything else remains secondary unless it directly supports these gates.
