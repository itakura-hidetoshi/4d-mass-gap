# MGAP4D GitHub Roadmap

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

## Phase 3: Proof hardening

- [x] Add Phase 3 proof-hardening plan and Lean tracking modules
- [x] Add OperatorAPI theorem-surface layer
- [x] Tighten OperatorAPI work-unit execution readiness
- [x] Add R1--R7 theorem-surface layers
- [x] Tighten R1--R7 concrete export/status exits against theorem surfaces
- [x] Add Global theorem-surface layer
- [x] Connect Global final assembly to Global theorem surface
- [x] Add theorem dependency map as checked Lean structures
- [x] Add local replay script for declaration counts
- [x] Restore internal deferred imports for Global/Concrete audit/status groups
- [x] Add Global/Concrete import root and summary surface
- [x] Connect FinalAssembly to Global/Concrete summary surface
- [x] Add Phase 3 theorem-surface and Global/Concrete checkpoint
- [x] Add first status-to-theorem replacement checkpoint
- [x] Complete replacement pass 1
- [x] Add replacement pass 2 plan
- [x] Complete replacement pass 2 bundle consolidation
- [x] Add replacement pass 2 closure checkpoint
- [x] Add Mathlib adoption gate
- [x] Add scoped Mathlib request records for R1/R2/R3/R4/R5/R6/R7
- [x] Add Mathlib request registry with R3 included
- [x] Add R1--R7 theorem candidates, checklists, proof-obligation maps, skeletons, bundles, and milestones
- [x] Add Phase3CandidateClosure for R1--R7 milestone coverage
- [x] Complete R1--R7 scoped Mathlib dry-run series and hold main adoption
- [x] Continue theorem-route hardening while main remains pre-Mathlib
- [x] Add post-Mathlib-hold theorem-route hardening checkpoint
- [x] Add R3--R7 route-specific hardening checkpoints
- [x] Add R3--R7 closure-candidate series review checkpoint
- [x] Add R3--R7 theorem-route queue checkpoint
- [x] Add R3--R7 theorem-route hardening passes
- [x] Add R3--R7 hardening pass series review checkpoint
- [x] Add post-hardening-pass closure checkpoint
- [x] Add R3 proof-obligation tightening sequence and closure
- [x] Observe R3 proof-obligation tightening closure main CI green
- [x] Record R3 proof-obligation tightening closure CI success in ledger
- [x] Add R4 proof-obligation tightening sequence and closure
- [x] Observe R4 proof-obligation tightening closure main CI green
- [x] Record R4 proof-obligation tightening closure CI success in ledger
- [x] Add R5 proof-obligation tightening sequence and closure
- [x] Observe R5 proof-obligation tightening closure main CI green
- [x] Record R5 proof-obligation tightening closure CI success in ledger
- [x] Add R6 proof-obligation tightening sequence and closure
- [x] Observe R6 proof-obligation tightening closure main CI green
- [x] Record R6 proof-obligation tightening closure CI success in ledger
- [x] Add R7 proof-obligation tightening sequence and closure
- [x] Observe R7 proof-obligation tightening closure main CI green
- [x] Record R7 proof-obligation tightening closure CI success in ledger
- [x] Add R3--R7 proof-obligation tightening closure series review checkpoint
- [x] Observe R3--R7 proof-obligation tightening closure series review main CI green
- [x] Record R3--R7 proof-obligation tightening closure series review CI success in ledger
- [ ] Add post-proof-obligation-tightening closure checkpoint
- [ ] Add Mathlib to main only after a separate explicit adoption proposal and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

The R1--R7 scoped Mathlib dry-run series has been reviewed. The decision is `hold_main_adoption`: dry-run success is accepted as Mathlib contact-surface buildability, not as theorem completion and not as permission to introduce Mathlib into `main`.

The post-Mathlib-hold theorem-route path has advanced through R3--R7 route-specific closure candidates, the theorem-route queue, R3--R7 hardening passes, R3--R7 hardening pass series review, post-hardening-pass closure, and R3/R4/R5/R6/R7 proof-obligation tightening closures. The R3--R7 proof-obligation tightening closure series review has also been observed green on `main`.

Observed current closure-series CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25778376405
Build job ID: 75715649304
Commit: c950ecb02b75530573530a5ef6f20d0baf787c40
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

Current invariant:

```text
main remains pre-Mathlib
Mathlib on main: not introduced
main-adoption decision: hold_main_adoption
R3--R7 proof-obligation tightening closure series review: CI green
R3--R7 theorem completions: not claimed
final gap theorem release: not unlocked
public theorem boundary: held
```

Next priority: add the post-proof-obligation-tightening closure checkpoint while preserving the pre-Mathlib invariant.
