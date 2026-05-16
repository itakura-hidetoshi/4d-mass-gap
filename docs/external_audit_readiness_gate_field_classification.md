# External audit readiness gate field classification

This document classifies each field of `ExternalAuditReadinessGateData` by witness type.

The purpose is to make the external-audit-readiness gate easier to review without overstating what each field proves.

This file is documentation-only. It does not modify Lean semantics. It does not open final theorem release. It does not claim independent external mathematical consensus.

## Witness classes

```text
theorem-derived
  A field whose current witness is a named Lean theorem, imported theorem, or theorem-like readiness object.

script-route
  A field whose current witness is supplied by the repository check route, CI replay route, or audit-script route.

documentation-route
  A field whose current witness is supplied by documented replay instructions, CI ledger notes, or source-tree review notes.

boundary-governance
  A field whose current witness preserves scope, release boundary, or external-consensus boundary.
```

## Field table

| Field | Current Lean type / witness | Witness class | Source / interpretation | Hardening target |
|---|---|---|---|---|
| `internalGateReady` | `internalReviewResidualClosureGateData.ready`, witnessed by `external_audit_readiness_internal_gate_ready_witness` | theorem-derived | Internal review closure gate readiness imported from `InternalReviewResidualClosureGate` | Keep theorem-derived; alias now exposes upstream theorem route. |
| `bundleManifestReady` | `finalTheoremReleaseBundleManifestReviewSurface.ready`, witnessed by `external_audit_readiness_bundle_manifest_ready_witness` | theorem-derived / documentation-route | Bundle manifest review surface readiness imported from `FinalTheoremReleaseBundleManifest` | Keep as manifest-level witness; document that it is bundle-surface readiness, not external acceptance. |
| `chainIndexReady` | `finalTheoremReleaseChainIndexReady`, witnessed by `external_audit_readiness_chain_index_ready_witness` | theorem-derived / documentation-route | Release chain index readiness imported with the bundle manifest surface | Keep as chain-index witness; alias now exposes exact origin route. |
| `repositoryInternalResidualClosed` | `True` | boundary-governance | Repository-level statement that the internal residual-closure route has been completed for the current checkpoint | Rename or document as `repositoryInternalResidualClosureCheckpointHeld`. |
| `noReviewLevelResidualLeft` | `True` | boundary-governance | Review-level residuals are not being silently reopened at this checkpoint | Rename or document as `noKnownReviewLevelResidualLeftAtCheckpoint`. |
| `independentReplayVisible` | `True` | documentation-route | Independent replay route is documented and visible | Rename or document as `independentReplayRouteDocumented`. |
| `auditScriptRouteVisible` | `True` | script-route | `scripts/check.sh` route is visible as the audit script path | Rename or document as `auditScriptRouteDocumented`. |
| `ciRouteVisible` | `True` | script-route / documentation-route | GitHub Actions CI route is documented as a replay route | Rename or document as `ciCheckpointDocumented`. |
| `externalAuditReady` | `True` | boundary-governance / documentation-route | A packet/readiness surface has been prepared for external audit | Rename or document as `externalAuditReadinessPacketPrepared`. |
| `externalConsensusNotClaimed` | `True` | boundary-governance | Explicitly blocks upgrade from internal CI readiness to external mathematical consensus | Rename or document as `externalConsensusBoundaryHeld`. |
| `publicBoundaryHeld` | `True` | boundary-governance | Public boundary remains held; no final public theorem release is opened by this gate | Keep or rename as `publicReleaseBoundaryHeld`. |
| `finalReleaseHeld` | `True` | boundary-governance | Final theorem release remains locked/review-gated | Keep or rename as `finalTheoremReleaseBoundaryHeld`. |
| `exactValuePreserved` | `exactGapValueReal = (33 : ℝ) / 20`, witnessed by `external_audit_readiness_exact_value_preserved_witness` | theorem-derived | Exact normalized value surface is preserved through the gate | Keep theorem-derived; alias now exposes the exact-value theorem route. |

## Current Lean witness aliases

```text
external_audit_readiness_internal_gate_ready_witness
external_audit_readiness_bundle_manifest_ready_witness
external_audit_readiness_chain_index_ready_witness
external_audit_readiness_exact_value_preserved_witness
```

These aliases are compatibility-preserving. They do not remove, rename, or reinterpret any `ExternalAuditReadinessGateData` field.

## Reviewer-facing interpretation

The final readiness conjunction should be read as a mixed witness packet:

```text
ExternalAuditReadinessGateData.ready
  = theorem-derived readiness
  + manifest / chain-index readiness
  + replay / script route visibility
  + release-boundary preservation
  + exact-value preservation
```

It should not be read as:

```text
external audit completed
external mathematical consensus obtained
final theorem release opened
all future residuals impossible
```

## Safe Lean hardening direction

A safe future Lean patch should avoid deleting fields. Instead it should add aliases or renamed fields while keeping compatibility.

Suggested compatibility-preserving approach:

```text
1. Add documentation-level theorem names that project each field.
2. Add comments above each `True` witness explaining its witness class.
3. Add an audit script check that this table mentions every field of `ExternalAuditReadinessGateData`.
4. Only then consider introducing renamed fields in a new structure version.
```

## Audit-script hardening target

A future audit can check that this file contains all field names:

```text
internalGateReady
bundleManifestReady
chainIndexReady
repositoryInternalResidualClosed
noReviewLevelResidualLeft
independentReplayVisible
auditScriptRouteVisible
ciRouteVisible
externalAuditReady
externalConsensusNotClaimed
publicBoundaryHeld
finalReleaseHeld
exactValuePreserved
```

and all witness classes:

```text
theorem-derived
script-route
documentation-route
boundary-governance
```

## CI checkpoint ledger

This checkpoint records the CI evidence for the witness-alias hardening patch before merge.

```text
PR: #14 Add external readiness witness aliases
Head commit: f2552d966973c0fa8ed6d2aab4903a3103d843ea
Merge commit: 1d7d55bc32096942b15c39f4725b8111e609aed4

Lean Direct Elan CI:
  Run ID: 25964521763
  Run number: 1907
  Result: success

Bridge Coherence CI:
  Run ID: 25964521761
  Run number: 215
  Result: success

External Audit Readiness CI:
  Run ID: 25964521766
  Run number: 93
  Result: success

Full Local Check CI:
  Run ID: 25964521762
  Run number: 191
  Result: success

Explicit full-check job reviewed:
  Run ID: 25964651676
  Job ID: 76325884534
  Job name: Run scripts/check.sh
  Result: success
```

Interpretation:

```text
The witness aliases are CI-green on the PR head.
The full local script route is green on the reviewed job.
The merge commit records the same patch through squash merge.
This ledger does not claim external mathematical consensus.
This ledger does not open final theorem release.
```

## Status

```text
Status: prepared
Semantic effect: documentation-only plus compatibility-preserving witness aliases
Lean semantics changed: no
External consensus claimed: no
Final theorem release opened: no
```
