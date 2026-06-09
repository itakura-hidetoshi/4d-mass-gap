# MGAP4D Roadmap

This roadmap tracks the current state and next review-gated steps of the canonical MGAP4D Lean proof repository.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open public final theorem release.

---

## Status snapshot as of 2026-06-09

The active front is now a two-lane hardening surface:

```text
R4 actual-Borel carrier / wrapper / closure
  -> genuine operator-valued spectral-measure API
  -> operator-topology countable additivity
  -> self-adjoint spectral theorem handoff

R5 compact centered plaquette observable
  -> direct review-ready decomposition
  -> direct-proof final export
  -> downstream input contract
  -> later R7 atom / positive-weight route
```

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
concrete l2 R2 local analytic lane: support/boundary layer, not spectral release
R4 finite-supported measurable local PVM phase: support/boundary layer completed
R4 actual Set ℝ endpoint carrier: present
R4 actual Borel endpoint set algebra: present
R4 actual Borel carrier wrapper: present as phase surface
R4 actual Borel wrapper closure: present as phase surface
R4 genuine operator-valued spectral measure: not yet claimed
R5 direct proof of compact/centered/smeared chosen-observable laws: present
R5 direct-proof downstream input contract: present and root-integrated
R7 exact atom / positive spectral weight: not yet claimed
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

Review principle:

```text
external-audit readiness is not external audit
replay success is not mathematical consensus
CI success is not proof review
documentation is not theorem body
finite-supported local PVM is not genuine spectral measure
actual Borel wrapper closure is not operator-topology countable additivity
formal-adjoint graph equality is not Mathlib IsSelfAdjoint promotion
R5 direct observable laws are not R7 atom/weight release
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

Status: **complete as internal theorem-body / proof-architecture surface**

- [x] Add spectral module entrypoint.
- [x] Add spectral gap formalization checkpoint.
- [x] Add exact gap analytic real closure.
- [x] Add Hilbert Rayleigh quotient theorem surface.
- [x] Add gap infimum / lower-bound / attainment surfaces.
- [x] Record exact normalized theorem-body value `33/20`.
- [x] Add scalar physical-Hamiltonian normalization.
- [x] Add operator physical-Hamiltonian normalization.
- [x] Preserve the distinction between normalized internal value and public final theorem acceptance.

Boundary retained:

```text
normalized value surface: 33/20
public final theorem release: not opened
```

---

## Phase C — Continuum-Hamiltonian proof-architecture surfaces

Status: **complete as internal proof-architecture / readiness surfaces**

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
- [x] Add four-lane residual closure.
- [x] Add internal review residual closure gate.
- [x] Add external audit readiness gate and replay certificate.

Boundary retained:

```text
continuum-Hamiltonian proof-architecture surfaces are present
public final theorem acceptance remains review-gated
```

---

## Phase D — Concrete l2 R2 local analytic support lane

Status: **support lane complete enough; boundary-held**

Purpose: keep the concrete `l2` R2 diagonal model as a narrow Mathlib-facing analytic support lane while preventing promotion from local graph/audit surfaces to global spectral/PVM/physical claims.

Completed on `main`:

- [x] Add the narrow current-route umbrella.
- [x] Close the old R2f graph-norm core blocker at the current route layer.
- [x] Add the residual-zero audit surface.
- [x] Document `R2_CURRENT_ROUTE.md` after residual-zero audit addition.
- [x] Add formal-adjoint graph candidate structure.
- [x] Add formal-adjoint operator-value surface.
- [x] Prove the formal-adjoint operator-value coordinate equation.
- [x] Prove graph-level equality between the completed diagonal graph carrier and the formal-adjoint graph candidate.

Active support-lane item:

- [ ] Merge or explicitly defer the R2 residual taxonomy review lane.

Boundary retained:

```text
closed operator theorem: not claimed
Mathlib IsSelfAdjoint theorem: not claimed
spectral theorem promotion: not claimed
PVM construction: not claimed
exact atom 33/20 derivation: not claimed
positive spectral weight: not claimed
physical Yang-Mills Hamiltonian promotion: not claimed
```

R2 should not remain the main thread unless it directly supports R4/R5/R7 obligations.

---

## Phase E — R4 finite-supported measurable local PVM scaffold

Status: **complete enough as scaffold and boundary**

Purpose: close the local finite-supported measurable PVM phase as a useful support object, not as the final spectral measure.

Completed:

- [x] Add R4 spectral-measure/PVM target API and obligation map.
- [x] Add operator-valued target specification and implementation checkpoints.
- [x] Add normalization / projection-valuedness / orthogonality / finite-additivity / countable-branch readings.
- [x] Add finite-supported measurable local spectral theorem and local full-axiom certificates.
- [x] Add Boolean compatibility, order laws, operator Boolean laws, spectral-integral Boolean laws, representation faithfulness/equivalence/completion, disjointness, and finite-additivity readings.
- [x] Add genuine handoff ledger, nonpromotion firewall, prerequisite gate, release packet, confirmed baseline packet, finality packet, and chain index for the finite-supported measurable phase.

Boundary retained:

```text
finite-supported measurable local PVM: scaffold / boundary
arbitrary Borel spectral measure: not claimed
operator-topology countable additivity: not claimed
self-adjoint spectral theorem handoff: not claimed
```

This phase should now be treated as a support base rather than the place to keep accumulating local shell artifacts.

---

## Phase F — R4 actual-Borel carrier and endpoint set algebra

Status: **complete enough; boundary-held**

Purpose: move from local finite-supported PVM scaffolding into actual Borel subsets of `ℝ`.

Completed / present:

- [x] Add actual endpoint carrier from spectral slots into `Set ℝ`.
- [x] Prove empty endpoint realizes `∅`.
- [x] Prove whole endpoint realizes `Set.univ`.
- [x] Prove endpoint measurability.
- [x] Add endpoint complement laws.
- [x] Add endpoint union laws.
- [x] Add endpoint intersection laws.
- [x] Add endpoint Boolean measurability closure.
- [x] Add public boundary after actual endpoint carrier.
- [x] Add public boundary after actual endpoint set algebra.

Representative files:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointCarrier.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointSetAlgebra.lean
```

Boundary retained:

```text
endpoint Set ℝ realization visible
endpoint measurability visible
endpoint Boolean set algebra visible
nonpromotion firewall visible
endpoint-only results do not imply arbitrary Borel spectral-measure construction
```

---

## Phase G — R4 arbitrary Borel carrier wrapper and closure

Status: **present as phase surfaces; boundary-held**

Purpose: pass from endpoint-only Borel objects to an arbitrary measurable-subset wrapper over `ℝ`, while still preserving the boundary before genuine operator-valued spectral measures.

Completed / present as phase surfaces:

- [x] Define actual Borel carrier wrapper:

```lean
def SpectralMeasurePVMActualBorelCarrierSet :=
  { s : Set ℝ // MeasurableSet s }
```

- [x] Add constructor for the wrapper.
- [x] Add empty and whole wrapper elements.
- [x] Add wrapper complement / union / intersection operations.
- [x] Lift endpoint slots into the actual Borel wrapper.
- [x] Prove wrapper operations forget to the corresponding `Set ℝ` operations.
- [x] Prove endpoint lifting compatibility with the endpoint carrier.
- [x] Add wrapper existence target.
- [x] Add wrapper Boolean closure target.
- [x] Add explicit closure witnesses for complement / union / intersection.
- [x] Add endpoint closure laws after forgetting to `Set ℝ`.
- [x] Add public boundary after wrapper and closure phase surfaces.

Representative files:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetWrapper.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelPhaseSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelClosurePhaseSurface.lean
```

Active / next:

- [ ] Keep root-export status explicit.
- [ ] Add theorem-index entries for wrapper and closure surfaces where still missing.
- [ ] Add audit hooks preventing wrapper closure from implying operator-topology countable additivity.
- [ ] Use this layer only as the carrier surface for the genuine operator-valued spectral-measure API.

Exit gate:

```text
arbitrary Borel wrapper surface visible
closure witnesses visible
endpoint lift compatibility visible
operator-topology countable-additivity boundary explicit
self-adjoint spectral-theorem boundary explicit
```

---

## Phase H — R4 genuine operator-valued spectral measure

Status: **active genuine analytic phase; not yet claimed complete**

Purpose: convert the actual Borel carrier/wrapper work into the real operator-valued PVM/spectral-measure layer, without skipping topology, countable additivity, or self-adjoint spectral theorem obligations.

Required obligations:

- [ ] State the target operator-valued spectral measure API.
- [ ] Specify the projection-valued codomain and equality notion.
- [ ] Specify the operator topology used for countable additivity.
- [ ] Add countable disjoint-union target for Borel subsets of `ℝ`.
- [ ] Prove or bridge monotonicity and finite-additivity laws in the actual Borel wrapper setting.
- [ ] Prove or bridge countable additivity in the selected operator topology.
- [ ] Connect the construction to the self-adjoint spectral theorem bridge.
- [ ] Add spectral-integral compatibility target.
- [ ] Add nonpromotion firewall for atom/weight/plaquette claims until the genuine PVM layer is available.

Exit gate:

```text
operator-valued PVM API stated
projection-valuedness stated/proved
operator-topology countable additivity stated/proved or explicitly held
self-adjoint spectral theorem handoff stated/proved or explicitly held
spectral integral compatibility stated/proved or explicitly held
R5/R7 promotion still blocked until genuine layer is ready
```

---

## Phase I — R5 compact centered plaquette observable direct-proof lane

Status: **partially root-integrated support lane; not atom/weight release**

Purpose: expose the compact centered plaquette observable through theorem-body proof, not through opaque review readiness, while preserving all atom/weight and R4 genuine-PVM boundaries.

Completed / present:

- [x] Add direct decomposition of compact-plaquette review-surface readiness.
- [x] Extract compact support for the R5 chosen observable.
- [x] Extract centeredness for the R5 chosen observable.
- [x] Extract smearing for the R5 chosen observable.
- [x] Package the compact / centered / smeared chosen-observable laws.
- [x] Transport the laws to the observable-atom chosen observable.
- [x] Add direct-proof final export.
- [x] Add public boundary for the direct-proof final export.
- [x] Add downstream input contract exposing both chosen-observable faces.
- [x] Preserve the boundary that this lane does not consume exact atom `33/20`.
- [x] Preserve the boundary that this lane does not consume positive spectral weight.
- [x] Preserve the R4 no-shell-to-full-collapse boundary.
- [x] Root-integrate the downstream input contract through `MGAP4D/R5/TheoremSurface.lean`.

Representative files:

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableReviewReadyDirectProof.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofFinalExport.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofDownstreamInputContract.lean
```

Still blocked:

- [ ] Consume the R5 downstream input against a genuine R4 operator-valued PVM surface.
- [ ] State operator-measure compatibility using the genuine spectral measure, not the local scaffold.
- [ ] Derive the exact `33/20` atom from theorem bodies, not from documentation or release packets.
- [ ] Prove positive spectral weight in the relevant observable/spectral-measure interface.
- [ ] Preserve the physical-normalization boundary.
- [ ] Add public-boundary wording preventing premature “mass gap solved” communication.

Exit gate:

```text
genuine R4 PVM layer available
R5 compact centered plaquette observable consumes the genuine PVM surface
exact atom 33/20 derived through theorem bodies
positive spectral weight proved through theorem bodies
physical-normalization boundary preserved
public final theorem boundary still review-gated
```

---

## Phase J — R7 exact atom / positive spectral weight route

Status: **downstream; blocked by R4 genuine PVM and R5 consumption gates**

Purpose: move from R5 compact centered plaquette support into exact atom and positive spectral weight only after the genuine spectral-measure obligations are available.

Required downstream steps:

- [ ] Define the R7 atom target against the genuine operator-valued spectral measure.
- [ ] Connect the atom route to the R5 downstream input contract.
- [ ] Prove exact atom `33/20` through theorem bodies.
- [ ] Prove positive spectral weight through theorem bodies.
- [ ] Preserve the no-documentation-shortcut rule.
- [ ] Preserve the physical-normalization boundary.
- [ ] Preserve public final theorem review gate.

Exit gate:

```text
R4 genuine PVM layer available
R5 direct-proof observable consumed correctly
R7 atom/exact-gap theorem body closed
positive spectral weight theorem body closed
public final theorem boundary still review-gated
```

---

## Phase K — Independent replay and external mathematical review

Status: **active governance layer**

Purpose: move from internal readiness to externally reproducible review without prematurely converting review success into public final theorem release.

- [ ] Run a fresh-clone replay on at least one second local machine.
- [ ] Record OS, CPU architecture, Lean version, Lake version, commit SHA, and complete command transcript.
- [ ] Add `docs/independent_replay_latest.md` as a compact append-only replay receipt.
- [ ] Keep `INDEPENDENT_REPLAY.md` command-first and current.
- [ ] Ask at least one external reviewer to run `bash scripts/check.sh`.
- [ ] Ask at least one reviewer to inspect `THEOREM_INDEX.md`.
- [ ] Ask at least one reviewer to inspect the physical-normalization boundary.
- [ ] Ask at least one reviewer to inspect the R4 actual-Borel carrier/wrapper front.
- [ ] Ask at least one reviewer to inspect the R4 genuine operator-valued spectral-measure obligations.
- [ ] Ask at least one reviewer to inspect the R5 direct-proof downstream input contract.
- [ ] Ask at least one reviewer to inspect the R7 atom/weight obligations before any public release wording changes.
- [ ] Collect review notes as append-only external audit notes.
- [ ] Preserve the rule: review success does not automatically open public final theorem release.

Exit gate:

```text
fresh-clone replay receipt present
external reviewer transcript present
major theorem-surface review notes present
normalization boundary review notes present
R4 actual-Borel review notes present
R4 genuine PVM obligation review notes present
R5 direct-proof review notes present
R7 atom/weight obligation review notes present
public-boundary wording unchanged
```

---

## Phase L — Audit-oriented version tag and Zenodo synchronization

Status: **pending**

- [ ] Choose an audit-oriented version name, for example `v1.6-audit` or the next appropriate audit tag.
- [ ] Confirm CI green on the exact commit to be tagged.
- [ ] Confirm `bash scripts/check.sh` from a fresh clone.
- [ ] Confirm `lake build` from a fresh clone.
- [ ] Confirm README / ROADMAP / THEOREM_INDEX / EXTERNAL_AUDIT_PACKET consistency.
- [ ] Confirm R4 actual-Borel wording does not overclaim genuine spectral-measure completion.
- [ ] Confirm R5 direct-proof wording does not overclaim exact atom / positive weight.
- [ ] Confirm R2 local analytic wording does not overclaim self-adjoint/spectral/PVM promotion.
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
R4 genuine spectral-measure boundary preserved
R5 atom/weight boundary preserved
R2 local analytic boundary preserved
```

---

## Public communication boundary

Status: **active governance rule**

Use:

```text
MGAP4D currently provides a Lean 4 proof architecture and replayable audit surface
for an internal normalized 4D mass-gap theorem-body route with normalized value 33/20.
The active analytic front is the R4 genuine operator-valued spectral-measure/PVM layer.
The R5 compact centered plaquette observable has a root-integrated direct-proof
downstream contract, but exact atom/positive-weight release remains blocked.
Public final theorem acceptance is not claimed.
```

Avoid wording that implies:

```text
external peer review completed
dimensional physical gap fixed without E0
CI output equals mathematical proof review
audit scripts replace Lean kernel checking
external-audit-readiness gate equals external audit
finite-supported local PVM implies genuine spectral measure
actual Borel wrapper closure implies operator-topology countable additivity
endpoint-only Borel surfaces imply arbitrary Borel spectral-measure construction
concrete l2 R2 residual-zero audit implies a closed operator theorem
formal-adjoint graph equality implies Mathlib self-adjointness
R5 compact/centered/smeared laws imply exact atom 33/20
R5 compact/centered/smeared laws imply positive spectral weight
R4/R5 current surfaces already imply public final theorem release
```

---

## Current priorities

1. Keep `README.md` and `ROADMAP.md` synchronized with the R4/R5 two-lane front.
2. State the genuine operator-valued spectral-measure API target explicitly.
3. State the operator topology for countable additivity before trying to discharge it.
4. Add or tighten audit hooks preventing wrapper closure from being read as countable additivity.
5. Keep `THEOREM_INDEX.md` synchronized for the R4 actual-Borel surfaces.
6. Add or tighten `THEOREM_INDEX.md` entries for the R5 direct-proof downstream contract.
7. Connect R5 only to a genuine R4 PVM surface, not to finite-supported local scaffolds.
8. Prepare the R7 atom/positive-weight route only after R4/R5 gates are explicit.
9. Keep R2 residual taxonomy as support, not the main thread.
10. Collect independent replay receipts.
11. Prepare an audit-oriented tag only after source-tree review and CI green confirmation.

---

## Stop condition

Do not expand the roadmap by adding new phases merely to make the project look larger.

The next mathematical movement should be narrow:

```text
R4 operator-valued spectral-measure API
R4 operator-topology countable-additivity target
R4 self-adjoint spectral theorem handoff
R5 direct-proof downstream contract review
R5 consumption against genuine R4 PVM
R7 exact atom / positive spectral weight route
```

Everything else remains secondary unless it directly supports these gates.
