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
- [ ] Add Mathlib only when theorem-level concrete modules require it
- [ ] Replace status-only surfaces by import-closed theorem surfaces
- [ ] Add independent CI matrix for stable Lean versions when feasible

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

Run CI after the Phase 3 checkpoint update. If green, the next technical step is preparing the first status-to-theorem replacement checkpoint before Mathlib adoption.
