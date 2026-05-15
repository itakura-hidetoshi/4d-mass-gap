# Mathlib bridge coherence workflow addition direct CI

Run ID: 25945521468
Audit job ID: 76272692295
Build job ID: 76272703776
Commit checked out by CI: f4837cc92af776036e7c15f4f1ab117cc1b11e77
Result: success

Status: Lean Direct Elan CI green.

Important note:
- This run is `Lean Direct Elan CI`, not `Bridge Coherence CI`.
- The new bridge-coherence artifacts are present in the checked-out commit.
- This run confirms repository audit/build health after adding the bridge-coherence workflow and documentation.
- This run does not execute `scripts/audit_bridge_coherence.py` because that script is wired into the separate `Bridge Coherence CI` workflow.

Confirmed audit steps in this run:
- Verify release manifest: success
- Audit Lean forbidden tokens: success
- Audit major theorem non-placeholder surface: success
- Summarize Lean replay surface: success

Forbidden-token audit result:
- Lean files scanned: 447
- sorry: 0
- admit: 0
- axiom: 0
- constant: 0
- Lean forbidden-token audit passed

Major theorem non-placeholder audit result:
- Major theorem specs audited: 12
- Major theorem non-placeholder audit passed

Replay summary:
- lean_files: 447
- imports: 1142
- declaration_like_lines: 2504
- namespace_lines: 918
- total_lines: 24665

Build confirmation:
- Build Lean project via direct elan: success
- lake build: success
- Lean 4.30.0-rc2
- Lake 5.0.0-src+3dc1a08

Bridge coherence artifacts present at checked-out commit:
- scripts/audit_bridge_coherence.py
- .github/workflows/bridge-coherence-ci.yml
- docs/mathlib_bridge_coherence_audit.md

Boundary:
- direct Lean CI green only
- bridge coherence audit execution requires a Bridge Coherence CI run
