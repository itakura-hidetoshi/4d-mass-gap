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
that the target / residual-filling / hardening-map layers by themselves complete the continuum proof
```

The current public boundary is an internal normalized theorem-body / proof-architecture surface with explicit audit, target-obligation, residual-filling, hardening-map, and replay support.

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

`elan` is the recommended way to install and select the pinned Lean toolchain.

## Fresh clone replay

From a clean directory:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
```

Confirm the pinned toolchain:

```bash
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
[check] replay summary
[check] lake update
[check] lake build
```

The command should exit with status `0`.

## Manual step-by-step replay

Reviewers who prefer to inspect each stage independently can run:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/replay_summary.py
lake update
lake build
```

### 1. Manifest verification

```bash
python3 scripts/verify_manifest.py
```

Expected result:

```text
archived manifest verification passed
```

This checks the repository's archived manifest surface.

### 2. Lean forbidden-token audit

```bash
python3 scripts/audit_lean_forbidden_tokens.py
```

Expected result:

```text
Lean forbidden-token audit passed
```

This checks Lean source files for forbidden proof-gap tokens outside comments and strings:

```text
sorry
admit
axiom
constant
```

### 3. Major theorem non-placeholder audit

```bash
python3 scripts/audit_major_theorem_nonplaceholder.py
```

Expected result:

```text
Major theorem non-placeholder audit passed
```

This is a syntactic theorem-surface audit. It checks that named load-bearing theorem statements are present and are not merely trivial `True` placeholders.

### 4. Analytic bridge-coherence audit

```bash
python3 scripts/audit_bridge_coherence.py
```

Expected result:

```text
Bridge coherence audit passed
```

This checks declared bridge files for expected import edges, ready surfaces, preservation anchors, positivity anchors, infinite-dimensional target obligations, and public-boundary anchors across the analytic / physical theorem chain.

### 5. Infinite-dimensional Yang-Mills target-layer audit

```bash
python3 scripts/audit_infinite_dimensional_target_layer.py
```

Expected result:

```text
Infinite-dimensional target layer audit passed
```

This checks that the repository's evolution beyond skeleton-only closure is represented as an explicit Lean target surface with named analytic obligations, root import, documentation ledger, and public-boundary markers.

### 6. Infinite-dimensional residual-filling bridge audit

```bash
python3 scripts/audit_infinite_dimensional_residual_filling.py
```

Expected result:

```text
Infinite-dimensional residual filling audit passed
```

This checks that immediately bridgeable residuals are connected through an imported Lean review surface, while hard physical residuals remain visible.

### 7. Hard physical residual hardening-map audit

```bash
python3 scripts/audit_hard_physical_residual_hardening_map.py
```

Expected result:

```text
Hard physical residual hardening map audit passed
```

This checks that the remaining hard physical residual is split into visible hardening lanes:

```text
hilbertConstructionLane
selfAdjointHPhysLane
continuumYangMillsLane
plaquetteSpectralWeightLane
```

### 8. Replay summary

```bash
python3 scripts/replay_summary.py
```

Expected result:

```text
Lean replay summary
wrote maps/REPLAY_SUMMARY_CURRENT.json
```

This summarizes the Lean replay surface.

### 9. Lake manifest and build

```bash
lake update
lake build
```

Expected result:

```text
Build completed successfully
```

`lake update` refreshes / confirms the Lake manifest for the pinned toolchain and declared dependencies. `lake build` is the Lean kernel build gate for the repository.

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
Summarize Lean replay surface
```

The build job runs:

```text
Confirm direct elan workflow
Install elan and Lean toolchain
Show Lean and Lake versions
Generate Lake manifest
Pull Mathlib cache when available
Build Lean project with lake build
```

The one-command local replay path is mirrored by:

```text
.github/workflows/full-local-check.yml
```

Thus the local `scripts/check.sh` path and the GitHub Actions audit/build paths intentionally cover the same core replay surfaces.

## Interpreting failures

### Failure in `verify_manifest.py`

The archived manifest surface is inconsistent with the repository state. Inspect the manifest and recent file additions/removals before interpreting theorem-level results.

### Failure in `audit_lean_forbidden_tokens.py`

A forbidden Lean token appears in source outside comments or strings. Treat this as a hard audit failure until removed or justified by a future policy change.

### Failure in `audit_major_theorem_nonplaceholder.py`

A load-bearing theorem surface may be missing, may have become a placeholder, or may have lost required anchors. Inspect the named theorem and its statement before trusting downstream bridge claims.

### Failure in `audit_bridge_coherence.py`

The analytic / physical bridge chain may have lost an expected import edge, ready surface, preservation anchor, positivity anchor, infinite-dimensional target anchor, or public-boundary anchor. Inspect the reported file and anchor.

### Failure in `audit_infinite_dimensional_target_layer.py`

The infinite-dimensional target layer may be missing, may not be imported by the analytic root, may lack required analytic-obligation anchors, or may be missing its documentation ledger.

### Failure in `audit_infinite_dimensional_residual_filling.py`

The residual-filling bridge may be missing, may not be imported by the analytic root, may lack required filled-surface anchors, or may be missing its documentation ledger.

### Failure in `audit_hard_physical_residual_hardening_map.py`

The hard residual hardening map may be missing, may not be imported by the analytic root, may hide one of the four hardening lanes, or may be missing its documentation ledger.

### Failure in `lake update`

The pinned toolchain or dependency manifest may not resolve. Confirm `lean-toolchain`, `lakefile.lean`, network availability, and Lake / elan installation.

### Failure in `lake build`

Lean kernel checking failed. This is the strongest local failure mode. Inspect the first Lean error and repair the corresponding source file before relying on audit summaries.

## Review boundary

A successful independent replay means:

```text
the repository builds with the pinned Lean toolchain
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-filling, and hardening-map checks pass
the replay summary is reproducible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
CI output alone is a substitute for proof review
the target / residual-filling / hardening-map layers alone complete the physical continuum proof
```

For external assessment, reviewers should combine this replay with direct inspection of the named theorem statements, bridge files, target layer, residual filling bridge, hardening map, documentation ledgers, and mathematical arguments.
