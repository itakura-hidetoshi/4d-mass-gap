# Tag creation script usage: Phase 3 pre-release hygiene CI green

This note explains how to use the bounded tag creation script and how to verify the tag after creation.

It does not create a tag. It does not open final theorem release. It does not claim R1--R7 theorem completion. It does not introduce Mathlib into `main`.

## Candidate

```text
Tag candidate: phase3-pre-release-hygiene-ci-green
Target commit: d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Script

```text
scripts/create_phase3_pre_release_hygiene_tag.sh
```

Run from the repository root:

```bash
bash scripts/create_phase3_pre_release_hygiene_tag.sh
```

The script is bounded to the candidate tag and target commit above. It checks for an existing local tag, refuses a mismatched local tag, creates an annotated tag only when needed, pushes the tag, and verifies that the resolved tag commit matches the expected target.

## Independent post-tag verification

After running the script, verify independently:

```bash
git fetch origin main --tags
git ls-remote --tags origin refs/tags/phase3-pre-release-hygiene-ci-green
git rev-list -n 1 phase3-pre-release-hygiene-ci-green
```

The resolved tag commit must be:

```text
d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Post-tag receipt template

Use this template only after the tag exists and resolves to the expected target commit:

```text
docs/post_tag_verification_receipt_phase3_pre_release_hygiene_ci_green_template.md
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
Status: usage note prepared
Semantic effect: documentation-only
Tag created: no
Final theorem release opened: no
Mathlib main adoption: no
```
