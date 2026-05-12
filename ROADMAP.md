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
- [x] Add R1 Hilbert concrete theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add R2 restriction concrete theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Correct R3 omission and add R3 requester/request/registry entry
- [x] Add R3 shifted / zero-form theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add R4 lower-bound theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add R5 spectrum / infimum theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add R6 interval-exclusion theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add R7 atom / exact-gap theorem candidate, checklist, proof-obligation map, skeleton, bundle, and milestone
- [x] Add Phase3CandidateClosure for R1--R7 milestone coverage
- [x] Add Mathlib request import cleanup for acyclic request files
- [x] Add Mathlib dry-run branch plan, checklist, execution note, and result ledger
- [x] Add pre-Mathlib closure checkpoint
- [x] Create R1 Mathlib dry-run draft PR
- [x] Record successful R1 dry-run result
- [x] Keep R1 dry-run PR as draft pending later review
- [x] Record current CI status observation as not confirmed
- [x] Open Phase 3 candidate-closure observation draft PR
- [x] Observe PR CI green for Phase 3 candidate closure
- [x] Record PR CI success in ledger and PR comment
- [x] Close Phase 3 observation PR unmerged after recording
- [x] Observe manual main workflow_dispatch CI green
- [x] Record manual main CI success in ledger
- [x] Add Phase3CIConfirmationClosure
- [x] Observe post-Phase3CIConfirmationClosure manual main workflow_dispatch CI green
- [x] Record post-confirmation CI success in ledger
- [x] Select R2 self-adjoint restriction as the next scoped Mathlib dry-run path
- [x] Open R2 Mathlib dry-run draft PR #3
- [x] Observe R2 dry-run CI green
- [x] Record R2 dry-run result in ledger and PR comment
- [x] Add PR #3 review / decision / keep-draft gate modules
- [x] Wire PR #3 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-PR3-gate-wiring main CI green
- [x] Select R3 shifted / zero-form as the next scoped Mathlib dry-run path
- [x] Open R3 Mathlib dry-run draft PR #4
- [x] Observe R3 dry-run CI green
- [x] Record R3 dry-run result in ledger and PR comment
- [x] Add PR #4 review / decision / hold-draft gate modules
- [x] Wire PR #4 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Select R4 lower-bound as the next scoped Mathlib dry-run path
- [x] Open R4 Mathlib dry-run draft PR #5
- [x] Observe R4 dry-run CI green
- [x] Record R4 dry-run result in ledger and PR comment
- [x] Add PR #5 review / decision / hold-draft gate modules
- [x] Wire PR #5 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-PR5-gate-wiring main CI green
- [x] Select R5 spectrum / infimum as the next scoped Mathlib dry-run path
- [x] Open R5 Mathlib dry-run draft PR #6
- [x] Observe R5 dry-run CI green
- [x] Record R5 dry-run result in ledger and PR comment
- [x] Add PR #6 review / decision / hold-draft gate modules
- [x] Wire PR #6 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-PR6-gate-wiring main CI green
- [x] Select R6 interval-exclusion as the next scoped Mathlib dry-run path
- [x] Open R6 Mathlib dry-run draft PR #7
- [x] Observe R6 dry-run CI green
- [x] Record R6 dry-run result in ledger and PR comment
- [x] Add PR #7 review / decision / hold-draft gate modules
- [x] Wire PR #7 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-PR7-gate-wiring main CI green
- [x] Select R7 atom / exact-gap as the next scoped Mathlib dry-run path
- [x] Open R7 Mathlib dry-run draft PR #8
- [x] Observe R7 dry-run CI green
- [x] Record R7 dry-run result in ledger and PR comment
- [x] Add PR #8 review / decision / hold gate modules
- [x] Wire PR #8 gate modules through `MGAP4D.MathlibAdoptionGate`
- [x] Add complete R1--R7 dry-run series review document
- [x] Add complete R1--R7 dry-run series review gate
- [x] Wire complete R1--R7 dry-run series review through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-series-review main CI green
- [x] Add Mathlib main-adoption review gate document
- [x] Add Mathlib main-adoption review Lean gate
- [x] Wire Mathlib main-adoption review gate through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-main-adoption-review-gate main CI green
- [x] Review complete R1--R7 dry-run series before any Mathlib main adoption decision
- [x] Record Mathlib main-adoption hold decision document
- [x] Add Mathlib main-adoption hold decision Lean gate
- [x] Wire Mathlib main-adoption hold decision through `MGAP4D.MathlibAdoptionGate`
- [x] Observe post-main-adoption-hold-decision main CI green
- [x] Continue theorem-route hardening while main remains pre-Mathlib
- [x] Add post-Mathlib-hold theorem-route hardening document
- [x] Add post-Mathlib-hold theorem-route hardening Lean checkpoint
- [x] Wire post-Mathlib-hold theorem-route hardening through top-level root
- [x] Observe post-Mathlib-hold theorem-route hardening main CI green
- [x] Add R3--R7 route-specific hardening checkpoints
- [x] Observe R3--R7 route-specific hardening main CI green
- [x] Add R3 shifted / zero-form closure-candidate checkpoint
- [x] Observe R3 closure-candidate main CI green
- [x] Add R4 lower-bound closure-candidate checkpoint
- [x] Observe R4 closure-candidate main CI green
- [x] Add R5 spectrum / infimum closure-candidate checkpoint
- [x] Observe R5 closure-candidate main CI green
- [x] Add R6 interval-exclusion closure-candidate checkpoint
- [x] Observe R6 closure-candidate main CI green
- [x] Add R7 atom / exact-gap closure-candidate checkpoint
- [x] Observe R7 closure-candidate main CI green
- [x] Add R3--R7 closure-candidate series review checkpoint
- [x] Observe R3--R7 closure-candidate series review main CI green
- [x] Add R3--R7 theorem-route queue checkpoint
- [x] Observe R3--R7 theorem-route queue main CI green
- [x] Add R3 shifted / zero-form theorem-route hardening pass
- [x] Observe R3 hardening pass main CI green
- [x] Add R4 lower-bound theorem-route hardening pass
- [x] Observe R4 hardening pass main CI green
- [x] Add R5 spectrum / infimum theorem-route hardening pass
- [x] Observe R5 hardening pass main CI green
- [x] Add R6 interval-exclusion theorem-route hardening pass
- [x] Observe R6 hardening pass main CI green
- [x] Add R7 atom / exact-gap theorem-route hardening pass
- [x] Observe R7 hardening pass main CI green
- [x] Add R3--R7 hardening pass series review checkpoint
- [x] Observe R3--R7 hardening pass series review main CI green
- [x] Add post-hardening-pass closure checkpoint
- [x] Observe post-hardening-pass closure main CI green
- [x] Record post-hardening-pass closure CI success in ledger
- [ ] Select the next proof-obligation tightening segment after post-hardening-pass closure
- [ ] Add Mathlib to main only after a separate explicit adoption proposal and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

The R1--R7 scoped Mathlib dry-run series has been reviewed. The decision is `hold_main_adoption`: dry-run success is accepted as Mathlib contact-surface buildability, not as theorem completion and not as permission to introduce Mathlib into `main`.

The post-Mathlib-hold theorem-route path has advanced through R3--R7 route-specific closure candidates, the theorem-route queue, R3--R7 hardening passes, R3--R7 hardening pass series review, and post-hardening-pass closure. All of those checkpoints have been observed green on `main`.

Observed current closure CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25732402911
Build job ID: 75560700359
Commit: e2a797bc00e244bb5369791167caec206113967f
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
R3--R7 hardening pass series: CI green
post-hardening-pass closure: CI green
R3--R7 theorem completions: not claimed
final gap theorem release: not unlocked
public theorem boundary: held
```

Next priority: select the next proof-obligation tightening segment after post-hardening-pass closure while preserving the pre-Mathlib invariant.
