# Audit-to-proof witness hardening plan

This document records the next hardening step after the MathlibAnalytic external-audit-readiness checkpoint.

The goal is not to expand the public theorem boundary. The goal is to reduce the amount of readiness metadata that is witnessed only by `True`, and to replace it step by step with named theorem-derived witnesses already present in the Lean chain.

This file is documentation-only. It does not create a tag. It does not open final theorem release. It does not claim external mathematical consensus.

## Current status

The repository already has a green external-audit-readiness checkpoint recorded in:

```text
docs/external_audit_readiness_gate_ci.md
```

The current source-tree review records that the CI-green proof checkpoint is:

```text
7041b000c4c8f30a2d99d5429504d00cffb88bcb
```

Later commits synchronize README / ROADMAP / tag-readiness / source-tree review documentation. A future tag should either target the CI-green proof checkpoint or wait for a fresh CI-green run on the latest documentation-synchronized commit.

## External-review pressure point

The current chain is strong as a proof-architecture repository because it has:

```text
- pinned Lean / mathlib lane
- `scripts/check.sh` replay path
- forbidden-token audit
- non-placeholder theorem-surface audit
- bridge-coherence audit
- residual-hardening audits
- external-audit-readiness gate
- CI ledger
- independent replay instructions
```

The main pressure point for external review is that some readiness predicates still contain metadata-like fields witnessed by `True`, for example:

```text
repositoryInternalResidualClosed := True
noReviewLevelResidualLeft := True
independentReplayVisible := True
auditScriptRouteVisible := True
ciRouteVisible := True
externalAuditReady := True
externalConsensusNotClaimed := True
publicBoundaryHeld := True
finalReleaseHeld := True
```

These are useful boundary markers, but a reviewer can reasonably ask which fields are mathematical/proof witnesses and which fields are documentation/governance witnesses.

## Hardening principle

Do not delete boundary fields.

Do not silently upgrade governance witnesses into mathematical witnesses.

Instead, split each field into one of three categories:

```text
A. theorem-derived witness
B. script/doc-route witness
C. explicit boundary/governance witness
```

Then make the category visible in names, documentation, and where practical in Lean definitions.

## Proposed staged patches

### Patch 1: naming clarification

Add explicit documentation tables for each final gate field:

```text
field name
current witness
witness class
source file
whether it is mathematical, script-level, or boundary-level
```

No Lean semantics change.

### Patch 2: theorem-derived witness extraction

For fields that already have upstream theorem names, add small projection theorems that expose the upstream origin rather than relying on a bare `True` witness.

Candidate fields:

```text
internalGateReady
bundleManifestReady
chainIndexReady
exactValuePreserved
finalReleaseHeld
publicBoundaryHeld
```

Expected result:

```text
ExternalAuditReadinessGateData.ready
```

still builds, but its proof body becomes visibly sourced from named upstream theorems where available.

### Patch 3: governance witness split

For fields that are not mathematical theorem claims, rename or duplicate them with explicit boundary language.

Candidate split:

```text
independentReplayVisible
  -> independentReplayRouteDocumented

auditScriptRouteVisible
  -> auditScriptRouteDocumented

ciRouteVisible
  -> ciCheckpointDocumented

externalAuditReady
  -> externalAuditReadinessPacketPrepared

externalConsensusNotClaimed
  -> externalConsensusBoundaryHeld
```

This makes it impossible for a reader to confuse documentation readiness with mathematical acceptance.

### Patch 4: audit script strengthening

Extend anchor audits so they do not only check that fields exist. They should also check that the documentation classifies each field as one of:

```text
theorem-derived
script-route
documentation-route
boundary-governance
```

This keeps the audit layer from overstating proof strength.

### Patch 5: CI-green retag candidate

After patches 1-4 pass:

```bash
bash scripts/check.sh
```

Then update the CI ledger with the fresh commit, run ID, job ID, and warning status.

Only after that, create a tag candidate.

## Non-goals

This plan does not claim:

```text
- external mathematical consensus
- independent peer-review completion
- Clay-style final theorem acceptance
- dimensional mass gap without E0
- that CI replaces proof review
- that readiness metadata is identical to theorem derivation
```

## Target outcome

After this hardening series, the repository should be easier for an external reviewer to read because each final gate field will say what kind of witness it is.

The final theorem boundary remains locked, but the audit-to-proof relationship becomes cleaner:

```text
proof-derived facts stay proof-derived
script facts stay script-level
documentation facts stay documentation-level
boundary facts stay boundary-level
```

This is the next safe step toward external replay and serious mathematical review.
