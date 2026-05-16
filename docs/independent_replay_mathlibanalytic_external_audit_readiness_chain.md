# Independent replay notes: MathlibAnalytic external-audit-readiness chain

This note gives a bounded independent replay path for the MathlibAnalytic external-audit-readiness checkpoint.

It is documentation-only. It does not open final theorem release. It does not claim independent external-audit completion. It does not create a version tag.

## Target checkpoint

```text
Repository: itakura-hidetoshi/4d-mass-gap
Proof checkpoint commit with CI green: 7041b000c4c8f30a2d99d5429504d00cffb88bcb
Workflow: Run scripts/check.sh
Run ID: 25961418682
Job ID: 76317232199
Result: success
```

Later README/ROADMAP/version-readiness/source-tree-review files may contain documentation synchronization commits. For proof replay, use the explicit checkpoint above unless a later commit has its own CI-green receipt.

## Toolchain

```text
Lean: 4.30.0-rc2
Lake: 5.0.0-src+3dc1a08
Toolchain commit: 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc
mathlib4: v4.30.0-rc2
```

## Replay command

From repository root:

```bash
bash scripts/check.sh
```

This runs the manifest check, forbidden-token audit, theorem-surface audits, bridge-coherence audits, hardening-lane audits, replay summary, `lake update`, the final gate target build, and `lake build`.

## Direct final-gate target

The final external-readiness target is:

```text
MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

Direct build command:

```bash
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## Expected replay summary at the CI-green checkpoint

```text
Lean files scanned: 457
Lean forbidden tokens: sorry=0, admit=0, axiom=0, constant=0
Major theorem specs audited: 12
Bridge files audited: 8
Ordered import edges audited: 5
Lean replay summary imports: 1191
Lean replay summary declaration_like_lines: 2602
Lean replay summary namespace_lines: 938
Lean replay summary total_lines: 27203
Build completed successfully: 8368 jobs
Final lake build: 0 jobs, success
Lean-side warnings in gate build: none observed
```

Small differences in wall-clock timing, cache download messages, and GitHub runner warnings are not proof-surface differences.

## Replay acceptance meaning

A successful independent replay confirms only:

```text
The pinned Lean/mathlib toolchain can build the repository checkpoint.
The declared audit scripts pass.
The final external-audit-readiness target builds.
The recorded theorem-surface and bridge-surface checks replay.
The public boundary remains explicitly review-gated.
```

It does not confirm:

```text
External mathematical consensus.
Independent peer-review acceptance.
Clay-style public final theorem acceptance.
A dimensional mass gap without an external reference scale E0.
That CI or replay alone replaces mathematical proof review.
That the final theorem release boundary is unlocked.
```

## Boundary

```text
Internal normalized exact value surface: 33/20
Pinned MathlibAnalytic lane: present
Final theorem release: locked / review-gated
External consensus: not claimed
External audit completion: not claimed
Tag created by this note: no
```