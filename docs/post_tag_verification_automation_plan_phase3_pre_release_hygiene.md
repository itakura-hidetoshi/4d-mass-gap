# Post-tag verification automation plan: Phase 3 pre-release hygiene CI green

This plan defines the bounded verification procedure to run after the prepared tag is created.

It does not create a tag. It does not open final theorem release. It does not claim R1--R7 theorem completion. It does not introduce Mathlib into `main`.

## Tag target

```text
Tag: phase3-pre-release-hygiene-ci-green
Expected target commit: d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Verification commands

Run after the tag has been created:

```bash
git fetch origin main --tags
git ls-remote --tags origin refs/tags/phase3-pre-release-hygiene-ci-green
git rev-list -n 1 phase3-pre-release-hygiene-ci-green
```

The final command must return exactly:

```text
d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Pass condition

```text
Remote tag exists: yes
Resolved tag commit: d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
Resolved tag commit matches expected target: yes
```

## Fail conditions

```text
Remote tag missing.
Resolved tag commit differs from expected target.
Tag exists only as a branch substitute.
Tag target is not d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b.
```

## Receipt to fill after pass

After verification passes, create a filled receipt from:

```text
docs/post_tag_verification_receipt_phase3_pre_release_hygiene_ci_green_template.md
```

The filled receipt should record:

```text
Remote tag observed: yes
Remote tag output: <paste command output>
Resolved tag commit: d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
Resolved tag matches expected target: yes
Verification date:
Verifier:
```

## Allowed tag meaning

```text
The Phase 3 pre-release hygiene checkpoint was recorded.
The source-tree review refresh for tag readiness had CI green evidence.
The repository remained pre-Mathlib at the target commit.
The public theorem boundary was preserved at the target commit.
```

## Disallowed tag meaning

```text
A public final theorem claim.
A claim that R1--R7 theorem completions are closed.
A claim that final gap theorem release is unlocked.
A Mathlib main-adoption decision.
A replacement for independent replay or external audit.
```

## Boundary invariants

```text
main remains pre-Mathlib.
lakefile.lean is not modified for Mathlib main adoption.
No active main-branch Lean module imports Mathlib.
Mathlib main-adoption decision remains hold_main_adoption.
R1--R7 theorem completions are not claimed.
Final gap theorem release is not unlocked.
Public theorem boundary remains review-gated.
```

## Current status

```text
Status: automation plan prepared
Semantic effect: documentation-only
Tag created: no
Final theorem release opened: no
Mathlib main adoption: no
```
