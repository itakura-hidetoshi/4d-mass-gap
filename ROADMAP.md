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
- [x] Add R1--R2 proof-obligation tightening bridge
- [x] Observe R1--R2 proof-obligation tightening bridge main CI green
- [x] Add R1 proof-obligation tightening sequence and closure
- [x] Observe R1 proof-obligation tightening closure main CI green
- [x] Add R2 proof-obligation tightening sequence and closure
- [x] Observe R2 proof-obligation tightening closure main CI green
- [x] Add R1--R7 proof-obligation tightening closure series review checkpoint
- [x] Observe R1--R7 proof-obligation tightening closure series review main CI green
- [x] Record R1--R7 proof-obligation tightening closure series review CI success in ledger
- [x] Add post-R1--R7 proof-obligation tightening closure checkpoint
- [x] Observe post-R1--R7 proof-obligation tightening closure main CI green
- [x] Record post-R1--R7 proof-obligation tightening closure CI success in ledger
- [x] Add final theorem release gate preparation refresh checkpoint
- [x] Observe final theorem release gate preparation refresh main CI green
- [x] Record final theorem release gate preparation refresh CI success in ledger
- [x] Add independent replay gate preparation checkpoint
- [x] Observe independent replay gate preparation main CI green
- [x] Record independent replay gate preparation CI success in ledger
- [x] Add independent replay protocol checkpoint
- [x] Observe independent replay protocol main CI green
- [x] Record independent replay protocol CI success in ledger
- [x] Add source-tree review gate checkpoint
- [x] Move release/replay/source-tree gates to global Phase3ReleaseGate root
- [x] Observe global Phase3ReleaseGate root main CI green
- [x] Record global Phase3ReleaseGate root CI success in ledger
- [x] Add source-tree review gate final sync checkpoint
- [x] Observe source-tree review gate final sync main CI green
- [x] Record source-tree review gate final sync CI success in ledger
- [x] Correct independent replay protocol to explicit R1--R7 global scope
- [x] Add independent replay protocol global scope correction checkpoint
- [x] Wire independent replay protocol global scope correction through Phase3ReleaseGate
- [x] Observe independent replay protocol global scope correction main CI green
- [x] Record independent replay protocol global scope correction CI success in ledger
- [x] Add external audit note gate checkpoint
- [x] Observe external audit note gate main CI green
- [x] Record external audit note gate CI success in ledger
- [x] Add entrypoint naming convention checkpoint
- [x] Wire entrypoint naming convention through Phase3ReleaseGate
- [x] Rename ambiguous R2 theorem root wording to R2 entrypoint wording
- [ ] Observe entrypoint naming convention main CI green
- [ ] Add external audit note appendix template
- [ ] Add Mathlib to main only after a separate explicit adoption proposal and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [ ] Add version tags only after CI green and source tree review
- [ ] Add external audit notes without changing active proof semantics

## Current priority

The R1--R7 scoped Mathlib dry-run series has been reviewed. The decision is `hold_main_adoption`: dry-run success is accepted as Mathlib contact-surface buildability, not as theorem completion and not as permission to introduce Mathlib into `main`.

Entrypoint naming is now fixed as follows: `MGAP4D.lean` is the global top-level Lean root, `MGAP4D/Phase3ReleaseGate.lean` is the global Phase 3 gate root, and `MGAP4D/R2/Theorem.lean` is the R2 restriction route entrypoint.

Current invariant:

```text
main remains pre-Mathlib
Mathlib on main: not introduced
main-adoption decision: hold_main_adoption
R2 entrypoint wording: adopted
R1--R7 theorem completions: not claimed
final gap theorem release: not unlocked
public theorem boundary: held
```

Next priority: confirm entrypoint naming convention CI while preserving the pre-Mathlib and review-gated invariants.
