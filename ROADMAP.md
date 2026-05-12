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
- [ ] Observe post-PR3-gate-wiring main CI green
- [ ] Select R3 shifted / zero-form as the next scoped Mathlib dry-run path after review
- [ ] Add Mathlib to main only after scoped dry-run success and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

The R1--R7 candidate-closure update, R3 correction, request import cleanup, and Phase3CIConfirmationClosure have been observed through CI.

Observed PR CI:

```text
PR: #2
Workflow: Lean Direct Elan CI
Run ID: 25712798053
Run number: 547
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
PR status: closed unmerged
```

Observed manual main workflow_dispatch CI before `Phase3CIConfirmationClosure`:

```text
Workflow: Lean Direct Elan CI
Run ID: 25713735152
Build job ID: 75499172664
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Observed manual main workflow_dispatch CI after `Phase3CIConfirmationClosure`:

```text
Workflow: Lean Direct Elan CI
Run ID: 25714521362
Build job ID: 75501432120
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Observed post-R2-dry-run ROADMAP main CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25716720759
Build job ID: 75508226598
Commit: 3c1d70882e78cd3248de5b08a1dc573df54b2fb0
Result: success
Generate Lake manifest: success
lake build: success
```

Observed R2 scoped Mathlib dry-run CI:

```text
PR: #3
Workflow: Lean Direct Elan CI
Run ID: 25716432314
Run number: 564
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
PR status: open draft, unmerged
```

PR #3 gate modules are now wired through:

```text
MGAP4D.MathlibAdoptionGate
```

This keeps the top-level `MGAP4D.lean` import surface stable while still routing the PR #3 gate chain through an already-imported root.

The current pre-Mathlib closure includes:

```text
R1 Hilbert
R2 restriction
R3 shifted / zero-form route
R4 lower bound
R5 spectrum / infimum
R6 interval exclusion
R7 atom / exact value
Phase3CandidateClosure
Phase3CIConfirmationClosure
R2 dry-run PR #3 result recorded
PR #3 gate chain wired through MathlibAdoptionGate
```

The earlier R3 omission has been corrected.

Next priority: observe post-PR3-gate-wiring main CI green, then select the R3 shifted / zero-form scoped Mathlib dry-run path after review. Main remains pre-Mathlib until a dry-run result is recorded, reviewed, and gated.
