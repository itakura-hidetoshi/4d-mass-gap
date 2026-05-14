# MGAP4D GitHub Roadmap

## Repository role

This repository is the canonical Lean proof repository for the 4D mass gap proof architecture.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS references this repository as a physics-facing bridge and public-core governance surface. KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final theorem release.

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
- [x] Add entrypoint naming convention final sync checkpoint
- [x] Observe entrypoint naming convention final sync main CI green
- [x] Record entrypoint naming convention final sync CI success in ledger
- [x] Add spectral module entrypoint
- [x] Add spectral gap formalization checkpoint
- [x] Wire spectral gap formalization gate through Phase3ReleaseGate
- [x] Observe spectral gap formalization main CI green
- [x] Record spectral gap formalization CI success in ledger
- [x] Add external audit note appendix template
- [x] Observe external audit note appendix template main CI green
- [x] Record external audit note appendix template CI success in ledger
- [x] Add KuuOS reference bridge
- [ ] Add Mathlib to main only after a separate explicit adoption proposal and review gate

## Phase 4: Release hygiene

- [x] Move release provenance into `docs/archive/`
- [x] Keep root README GitHub-native
- [x] Keep public theorem claims review-gated
- [x] Prepare version-tag readiness notes without creating a tag
- [x] Observe version-tag readiness notes main CI green
- [x] Record version-tag readiness notes CI success in ledger
- [x] Prepare version-tag source-tree review refresh without creating a tag
- [x] Observe version-tag source-tree review refresh main CI green
- [x] Record version-tag source-tree review refresh CI success in ledger
- [x] Prepare bounded tag-candidate receipt without creating a tag
- [x] Observe bounded tag-candidate receipt main CI green
- [x] Record bounded tag-candidate receipt CI success in ledger
- [x] Prepare manual tag creation receipt without creating a tag
- [x] Observe manual tag creation receipt main CI green
- [x] Record manual tag creation receipt CI success in ledger
- [x] Add bounded tag creation script without creating a tag
- [x] Add post-tag verification receipt template
- [x] Add tag creation script usage note without creating a tag
- [x] Observe tag creation script usage note main CI green
- [x] Record tag creation script usage note CI success in ledger
- [ ] Add version tags only after CI green and source tree review
- [x] Add external audit note template without changing active proof semantics
- [x] Record external audit note template CI without changing active proof semantics
- [ ] Add external audit notes without changing active proof semantics

## Current priority

The repository has reached a **spectral gap formalization CI green checkpoint** on `main`; the bounded external audit note appendix template has been observed CI green; version-tag readiness notes have been observed CI green; the version-tag source-tree review refresh has been observed CI green; the bounded tag-candidate receipt has been observed CI green; the manual tag creation receipt has been observed CI green; and the tag creation script usage note has also been observed CI green without creating a tag.

This checkpoint makes the normalized spectral value and witness surface visible inside Lean while preserving the review-gated theorem boundary:

```text
MGAP4D/Spectral.lean: spectral module entrypoint
MGAP4D/Spectral/GapFormalization.lean: spectral gap formalization checkpoint
MGAP4D/SpectralGapFormalizationGate.lean: Phase 3 spectral gap formalization gate
MGAP4D/Phase3ReleaseGate.lean: global Phase 3 gate including the spectral checkpoint
docs/external_audit_note_appendix_template.md: append-only external audit note template
docs/external_audit_note_appendix_template_ci.md: bounded CI ledger for the template update
docs/version_tag_readiness_notes.md: documentation-only version-tag readiness notes; no tag created
docs/version_tag_readiness_notes_ci.md: bounded CI ledger for the readiness note update
docs/version_tag_source_tree_review_refresh.md: documentation-only source-tree review refresh; no tag created
docs/version_tag_source_tree_review_refresh_ci.md: bounded CI ledger for the source-tree review refresh
docs/tag_candidate_receipt_phase3_pre_release_hygiene_ci_green.md: bounded tag-candidate receipt; no tag created
docs/tag_candidate_receipt_phase3_pre_release_hygiene_ci_green_ci.md: bounded CI ledger for the tag-candidate receipt
docs/tag_creation_manual_receipt_phase3_pre_release_hygiene_ci_green.md: manual tag creation receipt; tag not created by connected tool
docs/tag_creation_manual_receipt_phase3_pre_release_hygiene_ci_green_ci.md: bounded CI ledger for the manual tag creation receipt
scripts/create_phase3_pre_release_hygiene_tag.sh: bounded tag creation script
docs/post_tag_verification_receipt_phase3_pre_release_hygiene_ci_green_template.md: post-tag verification receipt template
docs/tag_creation_script_usage_phase3_pre_release_hygiene.md: tag creation script usage note
docs/tag_creation_script_usage_phase3_pre_release_hygiene_ci.md: bounded CI ledger for the usage note
docs/kuuos_reference_bridge.md: reference bridge from KuuOS to this canonical proof repository
```

Observed tag creation script usage note CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25840334487
Audit job ID: 75924127830
Build job ID: 75924137370
Commit: 8843365e96743b1319e0995a089bd80edf659204
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

Tag candidate receipt:

```text
Tag candidate: phase3-pre-release-hygiene-ci-green
Target commit: d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
Tag created: no
```

Manual tag command recorded:

```bash
git tag -a phase3-pre-release-hygiene-ci-green d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b -m "Phase 3 pre-release hygiene CI green"
git push origin phase3-pre-release-hygiene-ci-green
```

Current invariant:

```text
main remains pre-Mathlib
Mathlib on main: not introduced
main-adoption decision: hold_main_adoption
spectral gap formalization: CI green
spectral gap formalization gate: included in Phase3ReleaseGate
external audit note appendix template: CI green documentation-only surface
version-tag readiness notes: CI green documentation-only surface; no tag created
version-tag source-tree review refresh: CI green documentation-only surface; no tag created
tag-candidate receipt: CI green documentation-only surface; no tag created
manual tag creation receipt: CI green documentation-only surface; no tag created by connected tool
tag creation script: present; no tag created by this commit
tag creation script usage note: CI green documentation-only surface; no tag created
post-tag verification template: present; template only
KuuOS reference bridge: present; KuuOS references this repository as canonical proof repo
R1--R7 theorem completions: not claimed
final gap theorem release: not unlocked
public theorem boundary: held
```

Next priority: create the prepared bounded tag manually or with a GitHub surface that supports tag refs; after creation, add a post-tag verification receipt confirming the tag resolves to d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b.
