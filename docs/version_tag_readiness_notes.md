# Version tag readiness notes

This note prepares the repository for a future version tag decision after CI green and source-tree review.

It does not create a tag. It does not open final theorem release. It does not claim R1--R7 theorem completion. It does not introduce Mathlib into `main`.

## Current bounded checkpoint

```text
Repository: itakura-hidetoshi/4d-mass-gap
Branch: main
Active Lean root: MGAP4D.lean
Current phase: Phase 3 proof-hardening / release hygiene
Spectral gap formalization: CI green
External audit note appendix template: CI green documentation-only surface
MathlibAnalytic external audit readiness gate: CI green
```

## Current Lean-visible spectral surface

```text
MGAP4D/Spectral.lean
MGAP4D/Spectral/GapFormalization.lean
MGAP4D/SpectralGapFormalizationGate.lean
MGAP4D/Phase3ReleaseGate.lean
```

The normalized value surface is:

```text
normalizedGapValue.value = 33 / 20
```

This remains a structural checkpoint, not a final theorem-release claim.

## CI references

Spectral gap formalization CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25828960043
Build job ID: 75889136130
Commit: df99969343482d3030f6b6006edb082030dd1e87
Result: success
Ledger: docs/spectral_gap_formalization_ci.md
```

External audit note appendix template CI:

```text
Workflow: Lean Direct Elan CI
Run ID: 25830545961
Audit job ID: 75894216378
Build job ID: 75894235517
Commit: ea4627cee4883b5654164d521384086c792ea9bc
Result: success
Ledger: docs/external_audit_note_appendix_template_ci.md
```

MathlibAnalytic external audit readiness gate CI:

```text
Workflow: Run scripts/check.sh
Run ID: 25961050604
Job ID: 76316305600
Commit: 82195da8315d6b166ebdef24b3314be9ca969650
Result: success
Ledger: docs/external_audit_readiness_gate_ci.md
```

## Tag readiness criteria

A version tag may be considered only if all of the following are true.

```text
[ ] Current main commit has CI green.
[ ] Source-tree review is current for the commit to be tagged.
[ ] README and ROADMAP describe the same checkpoint state.
[ ] CI ledger exists for the commit or checkpoint being tagged.
[ ] No active main-branch Lean module imports Mathlib.
[ ] lakefile.lean has not been modified for Mathlib main adoption.
[ ] R1--R7 theorem completions are not claimed unless a separate theorem-completion gate is opened and reviewed.
[ ] Final gap theorem release remains locked unless a separate final-release gate is opened and reviewed.
[ ] Public theorem boundary remains review-gated pending independent replay and external audit.
```

## Allowed tag meaning

A tag prepared under this note may mean only:

```text
Phase 3 checkpoint state is reproducibly recorded.
The named checkpoint has CI green evidence.
The source-tree and documentation boundary are synchronized.
The public theorem boundary is preserved.
```

## Disallowed tag meaning

A tag prepared under this note must not be interpreted as:

```text
A public final theorem claim.
A claim that R1--R7 theorem completions are closed.
A claim that the final mass gap theorem release is unlocked.
A claim that Mathlib is adopted on main.
A replacement for independent replay or external audit.
```

## Suggested tag naming surface

The following are naming candidates only. No tag is created by this note.

```text
phase3-spectral-gap-formalization-ci-green
phase3-external-audit-template-ci-green
phase3-pre-release-hygiene-ci-green
phase3-mathlibanalytic-external-audit-readiness-ci-green
```

## Required pre-tag action

Before creating any version tag, record the exact target commit and CI run:

```text
Target commit:
Workflow:
Run ID:
Audit job ID, if applicable:
Build job ID:
Result:
Source-tree review note:
README synchronized: yes/no
ROADMAP synchronized: yes/no
```

## Boundary

```text
This readiness note is documentation-only.
No active proof semantics are changed.
No version tag is created here.
No final theorem release is opened.
No Mathlib main adoption is performed.
```
