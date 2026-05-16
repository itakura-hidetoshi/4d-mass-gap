# Independent Replay Guide

This document gives a minimal independent replay procedure for the MGAP4D Lean 4 repository.

It is intended for external reviewers who want to reproduce the repository-level audit and Lean build without relying on local, unpublished state.

## Scope

This guide checks the public repository state only.

It confirms:

```text
release manifest consistency
Lean forbidden-token audit
major theorem non-placeholder audit
analytic bridge-coherence audit
infinite-dimensional Yang-Mills target-layer audit
infinite-dimensional residual-filling bridge audit
hard physical residual hardening-map audit
Hilbert construction lane hardening audit
Lean replay summary generation
Lake manifest generation
Lean build via lake build
```

It does not by itself establish:

```text
external mathematical consensus
peer-review completion
Clay-style final theorem acceptance
a dimensional physical mass gap without choosing the reference scale E0
that syntactic audit scripts replace Lean kernel checking
that Lean CI replaces expert mathematical review
that the target / residual-filling / hardening-map / Hilbert-lane layers by themselves complete the continuum proof
```

The current public boundary is an internal normalized theorem-body / proof-architecture surface with explicit audit, target-obligation, residual-filling, hardening-map, Hilbert-lane hardening, and replay support.

## Required tools

The repository pins its Lean toolchain in:

```text
lean-toolchain
```

Current pinned toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Recommended local tools:

```text
git
python3
elan
```

## Fresh clone replay

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
cat lean-toolchain
lean --version
lake --version
```

Expected Lean family:

```text
Lean 4.30.0-rc2
Lake 5.0.0-src+3dc1a08 or compatible Lake for the pinned Lean toolchain
```

## One-command repository check

Run:

```bash
bash scripts/check.sh
```

This executes, in order:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit Hilbert construction lane hardening
[check] replay summary
[check] lake update
[check] lake build
```

The command should exit with status `0`.

## Manual step-by-step replay

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/audit_hilbert_construction_lane_hardening.py
python3 scripts/replay_summary.py
lake update
lake build
```

## Audit stages

### Manifest verification

```bash
python3 scripts/verify_manifest.py
```

Expected result:

```text
archived manifest verification passed
```

### Lean forbidden-token audit

```bash
python3 scripts/audit_lean_forbidden_tokens.py
```

Expected result:

```text
Lean forbidden-token audit passed
```

### Major theorem non-placeholder audit

```bash
python3 scripts/audit_major_theorem_nonplaceholder.py
```

Expected result:

```text
Major theorem non-placeholder audit passed
```

### Analytic bridge-coherence audit

```bash
python3 scripts/audit_bridge_coherence.py
```

Expected result:

```text
Bridge coherence audit passed
```

### Infinite-dimensional Yang-Mills target-layer audit

```bash
python3 scripts/audit_infinite_dimensional_target_layer.py
```

Expected result:

```text
Infinite-dimensional target layer audit passed
```

### Infinite-dimensional residual-filling bridge audit

```bash
python3 scripts/audit_infinite_dimensional_residual_filling.py
```

Expected result:

```text
Infinite-dimensional residual filling audit passed
```

### Hard physical residual hardening-map audit

```bash
python3 scripts/audit_hard_physical_residual_hardening_map.py
```

Expected result:

```text
Hard physical residual hardening map audit passed
```

### Hilbert construction lane hardening audit

```bash
python3 scripts/audit_hilbert_construction_lane_hardening.py
```

Expected result:

```text
Hilbert construction lane hardening audit passed
```

This checks that the Hilbert construction lane is split into hardened review surfaces:

```text
countableBasisHardened
finiteSpanDensityHardened
normTopologyHardened
cauchyCompletionHardened
completeNormedSpaceHardened
innerProductHardened
hilbertInstanceHardened
```

### Replay summary

```bash
python3 scripts/replay_summary.py
```

Expected result:

```text
Lean replay summary
wrote maps/REPLAY_SUMMARY_CURRENT.json
```

### Lake manifest and build

```bash
lake update
lake build
```

Expected result:

```text
Build completed successfully
```

## GitHub Actions parity

The main CI workflow is:

```text
.github/workflows/lean-direct-elan.yml
```

The audit job runs:

```text
Verify release manifest
Audit Lean forbidden tokens
Audit major theorem non-placeholder surface
Audit analytic bridge coherence
Audit infinite-dimensional Yang-Mills target layer
Audit infinite-dimensional residual filling bridge
Audit hard physical residual hardening map
Audit Hilbert construction lane hardening
Summarize Lean replay surface
```

The one-command local replay path is mirrored by:

```text
.github/workflows/full-local-check.yml
```

Thus the local `scripts/check.sh` path and the GitHub Actions audit/build paths intentionally cover the same core replay surfaces.

## Interpreting failures

```text
verify_manifest.py failure: archived manifest inconsistency
audit_lean_forbidden_tokens.py failure: forbidden Lean token found
audit_major_theorem_nonplaceholder.py failure: missing/placeholder theorem surface
audit_bridge_coherence.py failure: bridge anchor/import/boundary issue
audit_infinite_dimensional_target_layer.py failure: target layer/root/doc issue
audit_infinite_dimensional_residual_filling.py failure: residual-filling bridge/root/doc issue
audit_hard_physical_residual_hardening_map.py failure: hidden/missing hardening lane or doc issue
audit_hilbert_construction_lane_hardening.py failure: hidden/missing Hilbert construction sublane or doc issue
lake build failure: Lean kernel checking failed
```

## Review boundary

A successful independent replay means:

```text
the repository builds with the pinned Lean toolchain
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-filling, hardening-map, and Hilbert-lane checks pass
the replay summary is reproducible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
CI output alone is a substitute for proof review
the target / residual-filling / hardening-map / Hilbert-lane layers alone complete the physical continuum proof
```
