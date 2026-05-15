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

The current main branch records an internal normalized theorem-body surface:

```text
exactGapValueReal = 33 / 20
```

The value `33/20` is treated as theorem-body-origin, not as a packaging artifact, documentation artifact, CI ledger artifact, manifest-only artifact, or prototype-only wrapper.

Current boundary:

```text
internal normalized theorem-body claim: present
physical Hamiltonian normalization bridge: present
concrete residual closure: present
exact value theorem-body origin certificate: present
major theorem non-placeholder audit: green
bridge coherence audit: green
Lean Direct Elan CI: green
Bridge Coherence CI: green
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
- [x] Record Mathlib main-adoption decision: hold_main_adoption
- [x] Add post-Mathlib-hold theorem-route hardening checkpoint
- [x] Add R3--R7 route-specific hardening checkpoints
- [x] Add R3--R7 closure-candidate series review checkpoint
- [x] Add R3--R7 theorem-route queue checkpoint
- [x] Add R3--R7 theorem-route hardening passes
- [x] Add R3--R7 hardening pass series review checkpoint
- [x] Add post-hardening-pass closure checkpoint
- [x] Add R1--R7 proof-obligation tightening closures
- [x] Observe R1--R7 proof-obligation tightening closure series review main CI green
- [x] Record R1--R7 proof-obligation tightening closure series review CI success in ledger
- [x] Add post-R1--R7 proof-obligation tightening closure checkpoint
- [x] Observe post-R1--R7 proof-obligation tightening closure main CI green
- [x] Add final theorem release gate preparation refresh checkpoint
- [x] Observe final theorem release gate preparation refresh main CI green
- [x] Add independent replay gate preparation checkpoint
- [x] Add independent replay protocol checkpoint
- [x] Correct independent replay protocol to explicit R1--R7 global scope
- [x] Move release/replay/source-tree gates to global Phase3ReleaseGate root
- [x] Add source-tree review gate final sync checkpoint
- [x] Add external audit note gate checkpoint
- [x] Add entrypoint naming convention final sync checkpoint
- [x] Add spectral module entrypoint
- [x] Add spectral gap formalization checkpoint
- [x] Wire spectral gap formalization gate through Phase3ReleaseGate
- [x] Observe spectral gap formalization main CI green
- [x] Record spectral gap formalization CI success in ledger
- [x] Add external audit note appendix template
- [x] Add KuuOS reference bridge
- [ ] Add Mathlib to main only after a separate explicit adoption proposal and review gate

## Phase 4: Release hygiene and external-audit surfaces

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [x] Prepare version-tag readiness notes without creating a tag
- [x] Prepare version-tag source-tree review refresh without creating a tag
- [x] Prepare bounded tag-candidate receipt without creating a tag
- [x] Prepare manual tag creation receipt without creating a tag
- [x] Add bounded tag creation script without creating a tag
- [x] Add post-tag verification receipt template
- [x] Add tag creation script usage note without creating a tag
- [x] Open tag creation tracking issue without creating a tag
- [x] Record tag creation tracking issue receipt
- [x] Add post-tag verification automation plan without creating a tag
- [ ] Add version tags only after CI green and source tree review
- [x] Add external audit note template without changing active proof semantics
- [x] Record external audit note template CI without changing active proof semantics
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
- [x] Add final theorem release skeleton
- [x] Add final theorem release closure packet
- [x] Add final theorem release chain index
- [x] Add final theorem release bundle manifest
- [x] Add concrete residual closure
- [x] Observe concrete residual closure CI green
- [x] Record concrete residual closure CI in ledger

Concrete residual surfaces closed internally:

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

## Phase 6: Physical Hamiltonian normalization and exact-value origin

- [x] Add physical Hamiltonian normalization bridge
- [x] Observe physical Hamiltonian normalization bridge CI green
- [x] Record physical Hamiltonian normalization bridge CI in ledger
- [x] Add exact value theorem-body origin certificate
- [x] Observe exact value theorem-body origin CI green
- [x] Record exact value theorem-body origin CI in ledger
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

Key ledgers:

```text
docs/mathlib_physical_hamiltonian_normalization_bridge.md
docs/mathlib_physical_hamiltonian_normalization_bridge_ci.md
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
```

## Phase 7: Audit hardening

- [x] Add major theorem non-placeholder audit script
- [x] Wire major theorem non-placeholder audit into Lean Direct Elan CI
- [x] Fix positivity anchor for theorem-body closure audit
- [x] Observe major theorem non-placeholder audit CI green
- [x] Record major theorem non-placeholder audit CI in ledger
- [x] Add bridge coherence audit script
- [x] Add dedicated Bridge Coherence CI workflow
- [x] Trigger Bridge Coherence CI
- [x] Observe Bridge Coherence CI green
- [x] Record Bridge Coherence CI in ledger

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

Latest audit ledgers:

```text
docs/mathlib_major_theorem_nonplaceholder_audit.md
docs/mathlib_major_theorem_nonplaceholder_audit_ci.md
docs/mathlib_bridge_coherence_audit.md
docs/mathlib_bridge_coherence_ci.md
```

## Current priority

The repository has advanced from the earlier spectral checkpoint into an internal analytic theorem-body status:

```text
internal normalized theorem-body surface: present
exact value theorem-body origin: CI green
physical Hamiltonian normalization bridge: CI green
concrete residual closure: CI green
major theorem non-placeholder audit: CI green
Bridge Coherence CI: green
Lean Direct Elan CI: green
```

Current main-branch invariant:

```text
Dimensionless normalized exact value surface: 33/20
33/20 theorem-body origin: recorded
physical dimensional reading: requires E0
concrete Hilbert / H_phys / PVM / plaquette / operator-measure residuals: internally closed
Hilbert -> H_phys -> Yang-Mills -> spectral/PVM -> continuum bridge: mechanically audited
sorry/admit/axiom/constant: 0 in audited Lean source
major theorem placeholder audit: green
external consensus: not claimed
public final theorem claim: review-gated
```

Next priorities:

```text
1. Keep README, ROADMAP, and CI ledgers synchronized with main.
2. Extend local scripts/check.sh to include audit_major_theorem_nonplaceholder.py and audit_bridge_coherence.py if desired.
3. Prepare independent replay instructions for the current analytic theorem-body chain.
4. Add external audit notes without changing active proof semantics.
5. Add version tags only after source-tree review and CI green confirmation.
```
