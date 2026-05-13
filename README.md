# MGAP4D

MGAP4D is a Lean 4 repository for developing and checking the proof architecture of a normalized 4D mass gap theorem.

The repository is organized as a GitHub-native Lean project. The active source tree, CI, documentation, theorem-surface checkpoints, and migration history live directly in this repository.

## Repository role

This repository is the canonical Lean proof repository for the 4D mass gap proof architecture.

KuuOS references this repository as a physics-facing bridge and public-core governance surface:

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final theorem release.

## Current active Lean root

```text
MGAP4D.lean
```

The root imports the Phase 3 proof-hardening architecture, including the R1--R7 theorem-candidate surfaces, scoped Mathlib dry-run gates, post-Mathlib-hold theorem-route hardening, R1--R7 proof-obligation tightening closures, spectral gap formalization checkpoint, and the global Phase 3 release/replay/source-tree/external-audit gate root.

## Phase 3 status

The current `main` branch has reached a **spectral gap formalization CI green checkpoint** through the global Phase3ReleaseGate root.

The proof-hardening route has advanced through:

```text
TheoremSurface
  -> Replacement pass 1
  -> Replacement pass 2
  -> MathlibAdoptionGate
  -> R1--R7 theorem-candidate milestones
  -> Phase3CandidateClosure
  -> Phase3CIConfirmationClosure
  -> PreMathlibClosure
  -> R1--R7 scoped Mathlib dry-run series
  -> Mathlib main-adoption hold decision
  -> PostMathlibHoldTheoremHardening
  -> R3--R7 route-specific hardening
  -> R3--R7 theorem-route queue
  -> R3--R7 hardening pass series review
  -> PostHardeningPassClosure
  -> R3--R7 proof-obligation tightening closures
  -> R3--R7 proof-obligation tightening closure series review
  -> R1/R2 proof-obligation tightening bridge
  -> R1 Hilbert proof-obligation tightening closure
  -> R2 restriction proof-obligation tightening closure
  -> R1--R7 proof-obligation tightening closure series review
  -> PostR1R7ProofObligationTighteningClosure
  -> FinalTheoremReleaseGatePreparationRefresh
  -> IndependentReplayGatePreparation
  -> IndependentReplayProtocol
  -> IndependentReplayProtocolGlobalScopeCorrection
  -> SourceTreeReviewGate
  -> SourceTreeReviewGateFinalSync
  -> ExternalAuditNoteGate
  -> EntrypointNamingConvention
  -> EntrypointNamingConventionFinalSync
  -> SpectralGapFormalizationGate
  -> Phase3ReleaseGate
```

Important invariant:

```text
main remains pre-Mathlib
lakefile.lean is not modified for Mathlib
No active main-branch Lean module imports Mathlib
Mathlib main-adoption decision remains hold_main_adoption
R1--R7 theorem completions are not claimed
Final gap theorem release is not unlocked
Public theorem boundary remains review-gated
Spectral gap formalization is a structural checkpoint, not final theorem release
```

## Spectral gap formalization checkpoint

The current spectral checkpoint records a pre-Mathlib, route-neutral formalization surface for the normalized spectral gap value.

```text
MGAP4D/Spectral.lean: spectral module entrypoint
MGAP4D/Spectral/GapFormalization.lean: structural spectral gap formalization checkpoint
MGAP4D/SpectralGapFormalizationGate.lean: Phase 3 spectral gap formalization gate
MGAP4D/Phase3ReleaseGate.lean: global Phase 3 gate including the spectral checkpoint
```

The checkpoint includes:

```text
SpectralSector.vacuum
SpectralSector.orthogonal
SpectralGapFormalization
SpectralGapFormalization.ready
spectralGap3320Formalization
spectral_gap_formalization_pack
spectral_gap_3320_formalization_value
SpectralGapFormalizationGate
spectral_gap_formalization_gate_pack
```

Current formalized normalized value surface:

```text
normalizedGapValue.value = 33 / 20
```

Boundary condition:

```text
The spectral checkpoint makes the 33/20 normalized value and witness surface visible inside Lean.
It does not claim R1--R7 theorem completion.
It does not unlock the final gap theorem release.
It does not introduce Mathlib on main.
It preserves the public theorem boundary for independent replay and external audit.
```

## R1--R7 proof-obligation tightening and global gate status

```text
R1 Hilbert proof-obligation tightening closure: CI green
R2 restriction proof-obligation tightening closure: CI green
R3 proof-obligation tightening closure: CI green
R4 proof-obligation tightening closure: CI green
R5 proof-obligation tightening closure: CI green
R6 proof-obligation tightening closure: CI green
R7 proof-obligation tightening closure: CI green
R1--R7 proof-obligation tightening closure series review: CI green
Post-R1--R7 proof-obligation tightening closure: CI green
Final theorem release gate preparation refresh: CI green
Independent replay gate preparation: CI green
Independent replay protocol: CI green
Independent replay protocol global R1--R7 scope correction: CI green
Global Phase3ReleaseGate root: CI green
Source-tree review gate final sync: CI green
External audit note gate: CI green
Entrypoint naming convention final sync: CI green
Spectral gap formalization: CI green
External audit note appendix template: CI green
Version tag readiness notes: CI green, documentation-only, tag not created
KuuOS reference bridge: present
```

## Latest CI confirmation

```text
Version tag readiness notes CI
Workflow: Lean Direct Elan CI
Run ID: 25831588949
Audit job ID: 75897520855
Build job ID: 75897534901
Commit: 7f56509b1a027850fbf7ab79badfdfe80731563b
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

CI ledger:

```text
docs/version_tag_readiness_notes_ci.md
docs/external_audit_note_appendix_template_ci.md
docs/spectral_gap_formalization_ci.md
```

Recent CI ledger commit:

```text
283c7143aad0fa4f3fc5f914c16bc5adfd365b82
record version tag readiness notes CI
```

## Entrypoint and global gate structure

```text
MGAP4D.lean: global top-level Lean root
MGAP4D/Phase3ReleaseGate.lean: global Phase 3 release/replay/source-tree/external-audit gate root
MGAP4D/Spectral.lean: spectral module entrypoint
MGAP4D/Spectral/GapFormalization.lean: spectral gap formalization checkpoint
MGAP4D/SpectralGapFormalizationGate.lean: spectral gap formalization gate included by Phase3ReleaseGate
MGAP4D/R2/Theorem.lean: R2 restriction route entrypoint
IndependentReplayProtocol: R1--R7 global replay protocol
ExternalAuditNoteGate: external notes are review surfaces, not theorem completion or release authority
docs/external_audit_note_appendix_template.md: append-only external audit note template
docs/version_tag_readiness_notes.md: documentation-only version-tag readiness surface, no tag created
docs/kuuos_reference_bridge.md: reference bridge from KuuOS to this canonical proof repository
```

## Mathlib dry-run policy

Mathlib adoption may be tested only through scoped dry-run branches.

Dry-run success is accepted as contact-surface buildability only. It is not theorem completion and not permission to introduce Mathlib into `main`.

Relevant documents and modules include:

```text
docs/phase3_mathlib_main_adoption_hold_decision.md
docs/phase3_entrypoint_naming_convention.md
docs/phase3_entrypoint_naming_convention_final_sync.md
docs/entrypoint_naming_convention_final_sync_ci.md
docs/spectral_gap_formalization_ci.md
docs/external_audit_note_appendix_template.md
docs/external_audit_note_appendix_template_ci.md
docs/version_tag_readiness_notes.md
docs/version_tag_readiness_notes_ci.md
docs/kuuos_reference_bridge.md
MGAP4D/Phase3ReleaseGate.lean
MGAP4D/EntrypointNamingConvention.lean
MGAP4D/EntrypointNamingConventionFinalSync.lean
MGAP4D/Spectral.lean
MGAP4D/Spectral/GapFormalization.lean
MGAP4D/SpectralGapFormalizationGate.lean
```

## Build

```bash
lake update
lake build
```

For the full local audit sequence:

```bash
bash scripts/check.sh
```

The check script runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/replay_summary.py
lake update
lake build
```

GitHub Actions uses:

```text
Lean Direct Elan CI
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native documentation and checkpoint ledger
maps/                    Lightweight source and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Status

- GitHub-native Lean project: active
- CI: direct `elan` workflow
- Phase 3: spectral gap formalization CI green checkpoint reached
- Spectral module entrypoint: present
- Spectral gap formalization checkpoint: CI green
- Spectral gap formalization gate: included in Phase3ReleaseGate
- KuuOS reference bridge: present; KuuOS references this repository as canonical proof repo
- External audit note appendix template: CI green documentation-only surface
- Version tag readiness notes: CI green documentation-only surface; no tag created
- R1--R7 theorem-candidate milestones: recorded
- R3--R7 hardening pass series: CI green
- R1--R7 proof-obligation tightening closures: CI green
- Post-R1--R7 proof-obligation tightening closure: CI green
- Final theorem release gate preparation refresh: CI green
- Independent replay protocol: R1--R7 global scope corrected and CI green
- External audit note gate: CI green
- Entrypoint naming convention final sync: CI green
- Mathlib on main: not introduced
- Main-adoption decision: hold_main_adoption
- Final release: not opened
- Public final theorem claim: review-gated pending independent replay and external audit
