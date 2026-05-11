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
- [x] Add scoped Mathlib request records for R1/R2/R4/R5/R6/R7
- [x] Add Mathlib request registry
- [x] Add R1 Hilbert concrete theorem candidate
- [x] Add R1 Hilbert theorem checklist and proof-obligation map
- [x] Add R1 Hilbert theorem skeleton and milestone
- [x] Add Mathlib dry-run branch plan, checklist, execution note, and result ledger
- [x] Add pre-Mathlib closure checkpoint
- [ ] Run CI after pre-Mathlib closure and README/ROADMAP sync
- [ ] Create optional Mathlib dry-run branch for R1 Hilbert only
- [ ] Record dry-run result before any merge decision
- [ ] Add Mathlib to main only after scoped dry-run success and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

Run CI after the pre-Mathlib closure update. If green, the next technical step is an optional dry-run branch:

```text
feature/mathlib-r1-hilbert-dry-run
```

The dry-run branch may test Mathlib for the R1 Hilbert path, but `main` remains pre-Mathlib until the dry-run result is recorded, reviewed, and gated.
