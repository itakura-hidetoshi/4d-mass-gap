# Full Local Check CI Ledger

This ledger documents the GitHub Actions workflow that mirrors the external reviewer one-command replay path.

## Workflow

```text
Workflow name: Full Local Check CI
Workflow file: .github/workflows/full-local-check.yml
Main job: Run scripts/check.sh
```

## Purpose

The purpose of this workflow is to make the local external-review command and the CI replay path identical.

External reviewer command:

```bash
bash scripts/check.sh
```

CI command:

```bash
bash scripts/check.sh
```

This closes the gap between:

```text
what a reviewer is asked to run locally
what GitHub Actions verifies automatically
```

## Trigger policy

The workflow is configured for:

```text
workflow_dispatch
push to main
push to mathlib-adoption/exact-gap-analytic
pull_request to main
```

## Job outline

The main job performs:

```text
Checkout repository
Cache elan and Lake build artifacts
Install elan and Lean toolchain
Show Lean and Lake versions
Run full local check script
```

The final step runs:

```bash
bash scripts/check.sh
```

## Covered replay stages

Because the workflow invokes `scripts/check.sh`, it covers:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] replay summary
[check] lake update
[check] lake build
```

## Confirmed run

```text
Workflow: Full Local Check CI
Run ID: 25948605211
Job ID: 76281846717
Job name: Run scripts/check.sh
Commit checked out by CI: bd3111714d81b6e51615a7b912fec33c0a69d3bc
Result: success
Date: 2026-05-16
```

Confirmed job steps:

```text
Set up job: success
Checkout repository: success
Cache elan and Lake build artifacts: success
Install elan and Lean toolchain: success
Show Lean and Lake versions: success
Run full local check script: success
Complete job: success
```

Confirmed toolchain:

```text
Lean (version 4.30.0-rc2, x86_64-unknown-linux-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
Lake version 5.0.0-src+3dc1a08 (Lean version 4.30.0-rc2)
```

Confirmed `scripts/check.sh` replay:

```text
[check] verify manifest: archived manifest verification passed
[check] audit Lean forbidden tokens: passed; sorry=0, admit=0, axiom=0, constant=0; Lean files scanned=447
[check] audit major theorem non-placeholder surfaces: passed; Major theorem specs audited=12
[check] audit analytic bridge coherence: passed; Bridge files audited=7; Ordered import edges audited=4
[check] replay summary: generated maps/REPLAY_SUMMARY_CURRENT.json; lean_files=447; imports=1142; declaration_like_lines=2504; namespace_lines=918; total_lines=24665
[check] lake update: success
[check] lake build: Build completed successfully
```

## Audit meaning

A successful Full Local Check CI run means:

```text
the repository can execute the same replay path documented for external reviewers
the manifest verification passes
the forbidden-token audit passes
the major theorem non-placeholder audit passes
the analytic bridge-coherence audit passes
the replay summary is generated
the Lake manifest step succeeds
the Lean build succeeds
```

It does not mean:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
that audit scripts replace Lean kernel checking
that CI replaces expert mathematical review
```

## Relationship to other CI workflows

The repository also contains:

```text
.github/workflows/lean-direct-elan.yml
.github/workflows/bridge-coherence-ci.yml
```

`lean-direct-elan.yml` separates audit and build jobs.

`bridge-coherence-ci.yml` focuses on bridge-coherence audit surfaces.

`full-local-check.yml` verifies the external-review one-command replay as a single CI path.

## Review usage

External reviewers should record:

```text
Commit SHA:
Full Local Check CI run ID:
Full Local Check CI job ID:
Lean version:
Lake version:
scripts/check.sh result:
lake build result:
```

## Boundary

This ledger documents CI replay parity only.

The public theorem boundary remains review-gated. CI success is replay evidence, not external theorem acceptance.
