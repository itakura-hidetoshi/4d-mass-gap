# MGAP4D GitHub Roadmap

## Repository role

This repository is the canonical Lean proof repository for the MGAP4D normalized 4D mass gap proof architecture.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS references this repository as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final public theorem release.

## Current theorem claim and boundary

The current branch records an internal normalized theorem-body surface:

```text
exactGapValueReal = 33 / 20
```

The value `33/20` is treated as theorem-body-origin, not as a packaging artifact, documentation artifact, CI ledger artifact, manifest-only artifact, or prototype-only wrapper.

Current boundary:

```text
internal normalized theorem-body claim: present
physical Hamiltonian normalization bridge: present
concrete residual closure: present
infinite-dimensional residual filling bridge: present
complete infinite-dimensional Hilbert construction: present
Hilbert-to-physical unbounded operator bridge: present
self-adjoint HPhys bridge adoption: present
continuum Yang-Mills lane hardening: present
plaquette spectral weight lane hardening: present
continuum Hamiltonian mass-gap witness: present
continuum Hamiltonian exact mass-gap derivation: present
continuum Hamiltonian mass-gap theorem: present
continuum Hamiltonian mass-gap release adoption: present
continuum Hamiltonian complete mass-gap derivation: present
continuum Hamiltonian complete mass-gap release adoption: present
four-lane residual closure: present
internal review residual closure gate: present
external audit readiness gate: present
major theorem non-placeholder audit: green
bridge coherence audit: green
external mathematical consensus: not claimed
public final theorem claim: review-gated
```

The dimensional reading remains scale-dependent:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
internal units: E0 = 1, normalizedGap = 33/20
dimensional reading: physicalGap_dimensional = E0 * (33/20)
```

## Dependency lane status

The current Lake project uses a pinned MathlibAnalytic lane:

```text
Lean: 4.30.0-rc2
mathlib4: v4.30.0-rc2
roots: MGAP4D, MGAP4D.MathlibAnalytic
```

This supersedes older pre-Mathlib checkpoint language. The current boundary is not “Mathlib absent”; it is:

```text
MathlibAnalytic lane: adopted and pinned
Final theorem release: still locked / review-gated
External consensus: not claimed
Independent replay and external audit: still required
```

## Phase 1: GitHub-native project setup

- [x] Initialize Lean 4 Lake project
- [x] Add GitHub Actions using direct `elan`
- [x] Add audit scripts
- [x] Add active Lean scaffold
- [x] Import R1--R7 active root batch

## Phase 2: Source migration

- [x] Batch 001: active R1--R7 root files
- [x] Batch 002: lightweight docs and maps
- [x] Batch 003: snapshot root manifests
- [x] Batch 004: Global/Concrete status-only files
- [x] Batch 005: OperatorAPI interfaces
- [x] Batch 006: R1/Concrete files
- [x] Batch 007: R2/Concrete files
- [x] Batch 008: R3/R4/R5/R6/R7 Concrete files
- [x] Batch 009: Deferred import restoration plan and Mathlib policy
- [x] Batch 010: Archive prior kernels under a reviewed layout

## Phase 3: Proof hardening and spectral checkpoint

- [x] Add Phase 3 proof-hardening plan and Lean tracking modules
- [x] Add OperatorAPI theorem-surface layer
- [x] Add R1--R7 theorem-surface layers
- [x] Add Global theorem-surface layer
- [x] Add theorem dependency map as checked Lean structures
- [x] Complete replacement pass 1 and pass 2 closure
- [x] Add Mathlib adoption gate and request registry
- [x] Add R1--R7 theorem candidates, checklists, proof-obligation maps, skeletons, bundles, and milestones
- [x] Add Phase3CandidateClosure and Phase3CIConfirmationClosure
- [x] Complete R1--R7 scoped Mathlib dry-run series
- [x] Add spectral module entrypoint and spectral gap formalization checkpoint
- [x] Wire spectral gap formalization gate through Phase3ReleaseGate
- [x] Observe spectral gap formalization CI green
- [x] Add KuuOS reference bridge

## Phase 4: Release hygiene and external-audit surfaces

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [x] Prepare tag-readiness notes without creating a tag
- [x] Add external audit note template without changing active proof semantics
- [x] Record external audit readiness gate CI without changing active proof semantics
- [x] Add continuum Hamiltonian complete release surface without changing active proof semantics
- [ ] Add version tags only after fresh source-tree review and CI green confirmation for the target commit
- [ ] Add external audit notes without changing active proof semantics

## Phase 5: Analytic theorem-body and concrete residual closure

- [x] Add exact gap analytic real closure
- [x] Add Hilbert Rayleigh quotient theorem surface
- [x] Add self-adjoint `H_phys` theorem surface
- [x] Add spectral theorem theorem surface
- [x] Add PVM theorem surface
- [x] Add observable atom theorem surface
- [x] Add compact plaquette construction theorem surface
- [x] Add operator-measure compatibility theorem surface
- [x] Add exact gap theorem-body closure
- [x] Add concrete Hilbert realization theorem
- [x] Add concrete `H_phys` realization theorem
- [x] Add infinite-dimensional Hilbert necessity from P≠NP bridge
- [x] Add arbitrarily large excitation family
- [x] Add Hilbert linear independence from excitations
- [x] Add Hilbert countable basis skeleton
- [x] Add Hilbert finite-span density skeleton
- [x] Add Hilbert norm topology skeleton
- [x] Add Hilbert Cauchy completion skeleton
- [x] Add Hilbert complete normed-space skeleton
- [x] Add Hilbert inner-product skeleton
- [x] Add Hilbert-space instance skeleton
- [x] Add physical unbounded-operator skeleton
- [x] Add concrete Yang-Mills Hamiltonian skeleton
- [x] Add spectral realization skeleton
- [x] Add continuum spectral theorem skeleton
- [x] Add final theorem release skeleton / closure / chain index / bundle manifest
- [x] Add concrete residual closure
- [x] Observe concrete residual closure CI green

Concrete residual surfaces closed internally:

```text
concrete Hilbert realization
concrete H_phys / unbounded-operator realization
spectral measure / PVM exact-atom realization
compact lattice-gauge plaquette observable construction
operator-measure realization and compatibility
```

## Phase 6: Physical Hamiltonian normalization and exact-value origin

- [x] Add physical Hamiltonian normalization bridge
- [x] Add exact value theorem-body origin certificate
- [x] Align README theorem claim and boundary with internal theorem-body status
- [x] Sync README with current main status
- [x] Sync ROADMAP with current theorem-body status

Normalization invariant:

```text
reference energy scale E0 is explicit and positive
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
internal normalized units set E0 = 1
dimensionless exact gap is 33/20
dimensional physical gap reads as E0 * 33/20
```

Exact-value origin invariant:

```text
33/20 is read from ExactGapTheoremBodyClosure.exactValue_eq_3320
33/20 is not treated as packaging artifact
33/20 is not treated as documentation artifact
33/20 is not treated as CI-ledger artifact
33/20 is not treated as manifest-only artifact
observable spectral weight positivity is carried from theorem body
PVM mass compatibility is carried from theorem body
```

## Phase 7: Audit hardening

- [x] Add major theorem non-placeholder audit script
- [x] Wire major theorem non-placeholder audit into CI
- [x] Add bridge coherence audit script
- [x] Add dedicated Bridge Coherence CI workflow
- [x] Wire expanded audit chain into `scripts/check.sh`
- [x] Add external audit readiness field-classification audit
- [x] Add external audit readiness replay-certificate audit

Audit invariants:

```text
major theorem surfaces do not use sorry/admit/axiom/constant
major theorem surfaces are not trivial True-only statements
33/20 theorem-body origin is checked as a non-placeholder statement
operator-measure/PVM compatibility is checked as a non-placeholder statement
Hamiltonian normalization bridge is checked as a non-placeholder statement
complete Hilbert -> physical unbounded operator -> H_phys -> Yang-Mills -> spectral/PVM -> continuum route is mechanically audited
exact value preservation anchors are mechanically audited
public boundary markers are mechanically audited
external audit readiness is mechanically gated
```

## Phase 8: External audit readiness hardening chain

- [x] Add infinite-dimensional Yang-Mills realization target layer
- [x] Add infinite-dimensional residual filling bridge
- [x] Add hard physical residual hardening map
- [x] Replace the former Hilbert construction lane hardening route with `CompleteInfiniteDimensionalHilbertConstruction`
- [x] Add Hilbert-to-physical unbounded operator bridge
- [x] Add self-adjoint HPhys bridge adoption
- [x] Add self-adjoint HPhys lane hardening
- [x] Add continuum Yang-Mills lane hardening
- [x] Add plaquette spectral weight lane hardening
- [x] Add continuum Hamiltonian mass-gap witness
- [x] Add continuum Hamiltonian exact mass-gap derivation
- [x] Add continuum Hamiltonian mass-gap witness hardening
- [x] Add continuum Hamiltonian mass-gap theorem
- [x] Add continuum Hamiltonian mass-gap release adoption
- [x] Add continuum Hamiltonian complete mass-gap derivation
- [x] Add continuum Hamiltonian complete mass-gap release adoption
- [x] Add four-lane residual closure
- [x] Add internal review residual closure gate
- [x] Add external audit readiness gate
- [x] Build `MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate` in CI
- [x] Sync README, ROADMAP, independent replay, external audit packet, external review checklist, theorem index, and source-tree receipt to complete Hilbert route
- [ ] Add version tags only after fresh source-tree review and CI green confirmation for the exact target commit

Current external-audit-readiness checkpoint:

```text
Workflow: Full Local Check CI / Run scripts/check.sh
Run ID: 25991097002
Head commit: 511f63477081bec49a5291cb77a2769b3d154c01
Result: success
Lean files scanned: 472
sorry/admit/axiom/constant: 0/0/0/0
Major theorem specs audited: 12
Bridge files audited: 8
Ordered import edges audited: 5
Continuum Hamiltonian exact mass-gap derivation build: success
Continuum Hamiltonian release-chain addendum build: success
External audit readiness gate build: success
Final lake build: success
```

## Current priority

```text
1. Wait for fresh CI on the latest documentation head.
2. Confirm scripts/check.sh is green on that exact head or merge ref.
3. Confirm external audit readiness CI is green on that exact head or merge ref.
4. Record the exact latest head / merge ref in the CI ledger if it differs from the previous green checkpoint.
5. Add external audit notes without changing active proof semantics.
6. Add version tags only after source-tree review and CI green confirmation for the exact target commit.
```

Current branch invariant:

```text
Dimensionless normalized exact value surface: 33/20
33/20 theorem-body origin: recorded
physical dimensional reading: requires E0
concrete Hilbert / H_phys / PVM / plaquette / operator-measure residuals: internally closed
infinite-dimensional target and residual-filling surfaces: recorded
complete infinite-dimensional Hilbert construction: recorded
Hilbert-to-physical unbounded operator bridge: recorded
self-adjoint HPhys bridge adoption: recorded
continuum-Hamiltonian positive exact mass-gap theorem: recorded
continuum-Hamiltonian complete mass-gap derivation: recorded
continuum-Hamiltonian complete release adoption: recorded
external audit readiness gate: recorded
complete Hilbert -> H_phys -> Yang-Mills -> spectral/PVM -> continuum -> continuum-Hamiltonian theorem bridge: mechanically audited
sorry/admit/axiom/constant: 0 in audited Lean source
major theorem placeholder audit: green
external consensus: not claimed
public final theorem claim: review-gated
```
