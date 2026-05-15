# Mathlib major theorem non-placeholder audit CI

Run ID: 25945038254
Audit job ID: 76271219435
Build job ID: 76271230435
Commit checked out by CI: 7df8b6fb47e9fb136081782b0d893244cd43abc3
Result: success

Status: CI green.

Confirmed audit steps:
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
- Forbidden Lean tokens audited: sorry/admit/axiom/constant
- Trivial theorem statement audit: theorem ... : True :=
- Statement-anchor audit: exact value, positivity, spectralWeight, PVM mass, normalization
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

Meaning:
- major theorem surfaces are checked against axiom/sorry/admit/constant
- major theorem surfaces are checked against trivial True-only statements
- 33/20 theorem-body origin is checked as a non-placeholder statement
- operator-measure/PVM compatibility is checked as a non-placeholder statement
- Hamiltonian normalization bridge is checked as a non-placeholder statement
- Lean kernel build is green

Boundary:
- syntactic CI audit plus Lean build confirmation
- not a replacement for theorem-body proof review
- public theorem boundary is held
