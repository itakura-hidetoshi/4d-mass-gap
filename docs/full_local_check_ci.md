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

Because the workflow invokes `scripts/check.sh`, it covers the full reviewer replay path, including:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit proof placeholder inventory
[check] audit final physical carrier routing
[check] audit analytic bridge coherence
[check] audit hard physical residual ledger
[check] audit external audit readiness gate
[check] audit external audit readiness gate field classification
[check] audit external audit readiness replay certificate
[check] audit OS/Wightman mass-gap bridge
[check] replay summary
[check] lake update
[check] build external audit readiness gate
[check] build OS/Wightman mass-gap external audit bridge
[check] build Euclidean Yang-Mills measure to mass-gap pipeline
[check] build unconditional Euclidean Yang-Mills measure target
[check] build Euclidean Yang-Mills measure construction spine
[check] build Euclidean Yang-Mills construction external audit bridge
[check] build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge
[check] lake build
```

The OS/Wightman / Euclidean construction replay subroute is:

```text
ExternalAuditReadinessGate
  -> OSWightmanMassGapExternalAuditBridge
  -> EuclideanYangMillsMeasureToMassGapPipeline
  -> EuclideanYangMillsMeasureUnconditionalTarget
  -> EuclideanYangMillsMeasureConstructionSpine
  -> EuclideanYangMillsMeasureConstructionExternalAuditBridge
```

## Current replay interpretation

A current successful run of `bash scripts/check.sh` means that the following surfaces are replayed together:

```text
forbidden-token audits
major theorem non-placeholder audits
proof placeholder inventory
bridge-coherence audits
final physical carrier routing
OS/Wightman mass-gap bridge audit
THEOREM_INDEX.md route anchors
EXTERNAL_REVIEW_CHECKLIST.md route anchors
external audit readiness gate
OS/Wightman external audit bridge
Euclidean measure conditional pipeline
Euclidean measure unconditional-construction target
finite-volume/continuum construction spine
construction-spine external-audit projection
full Lean build
```

It still does not mean external mathematical acceptance of the Euclidean Yang--Mills measure construction, the OS/Wightman bridge, or the construction-spine external-audit projection.

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

The confirmed run above predates the OS/Wightman--Euclidean construction external-audit bridge additions. New reviewers should record a fresh run against the current commit before treating this ledger as current replay evidence.

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

Historical confirmed `scripts/check.sh` replay:

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

A successful current Full Local Check CI run means:

```text
the repository can execute the same replay path documented for external reviewers
the manifest verification passes
the forbidden-token audit passes
the major theorem non-placeholder audit passes
the proof placeholder inventory passes
the analytic bridge-coherence audit passes
the OS/Wightman mass-gap bridge audit passes
the THEOREM_INDEX.md OS/Wightman--Euclidean construction route anchors pass
the EXTERNAL_REVIEW_CHECKLIST.md construction external-audit anchors pass
the replay summary is generated
the Lake manifest step succeeds
the OS/Wightman external bridge builds
the Euclidean measure conditional pipeline builds
the Euclidean measure unconditional-construction target builds
the finite-volume/continuum construction spine builds
the construction-spine external-audit projection builds
the Lean build succeeds
```

It does not mean:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
that audit scripts replace Lean kernel checking
that CI replaces expert mathematical review
that the Euclidean Yang-Mills measure has been externally accepted
that the OS/Wightman bridge has been externally accepted
that the construction-spine external-audit projection is itself external acceptance
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
OS/Wightman mass-gap bridge audit result:
Euclidean construction external audit bridge build result:
lake build result:
```

## Boundary

This ledger documents CI replay parity only.

The public theorem boundary remains review-gated. CI success is replay evidence, not external theorem acceptance.
