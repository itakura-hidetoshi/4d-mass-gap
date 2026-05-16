# MGAP4D External Audit Packet

This packet is the top-level navigation surface for external audit and independent replay of the MGAP4D repository.

It collects the repository's current audit-facing documents into one ordered route.

## Boundary statement

The current repository state is an internal normalized theorem-body / proof-architecture surface with explicit replay, theorem-surface audit, bridge-coherence audit, and physical-realization boundary markers.

It does not claim:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI output replaces mathematical review
that audit scripts replace Lean kernel checking
```

## Primary review route

Reviewers should read and execute in this order:

| Step | File / command | Purpose |
|---:|---|---|
| 1 | `README.md` | Understand repository role, current theorem claim, CI/audit status, and public boundary. |
| 2 | `EXTERNAL_REVIEW_CHECKLIST.md` | Follow the ordered review checklist. |
| 3 | `INDEPENDENT_REPLAY.md` | Reproduce the repository-level replay from a fresh clone. |
| 4 | `bash scripts/check.sh` | Run the complete local replay path. |
| 5 | `.github/workflows/full-local-check.yml` | Confirm that the same one-command replay path is mirrored in GitHub Actions. |
| 6 | `THEOREM_INDEX.md` | Inspect the 12 major theorem surfaces and 7 bridge surfaces. |
| 7 | `PHYSICAL_REALIZATION_BOUNDARY.md` | Interpret `PUnit`, singleton, prototype, and skeleton surfaces correctly. |
| 8 | `docs/` ledgers | Compare source statements with audit and CI documentation ledgers. |

## One-command replay

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
```

Expected high-level stages:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] replay summary
[check] lake update
[check] lake build
```

## CI parity for the one-command replay

The one-command local replay path is mirrored in GitHub Actions by:

```text
.github/workflows/full-local-check.yml
```

Workflow name:

```text
Full Local Check CI
```

Main job:

```text
Run scripts/check.sh
```

This workflow installs / exposes the pinned Lean toolchain, prints Lean and Lake versions, and then runs:

```bash
bash scripts/check.sh
```

This gives reviewers a CI-level check of the same command that `INDEPENDENT_REPLAY.md` asks them to run locally.

## Manual replay path

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/replay_summary.py
lake update
lake build
```

## Audit scripts

| Script | Audit role |
|---|---|
| `scripts/verify_manifest.py` | Checks archived manifest consistency. |
| `scripts/audit_lean_forbidden_tokens.py` | Checks Lean source for forbidden proof-gap tokens outside comments / strings. |
| `scripts/audit_major_theorem_nonplaceholder.py` | Checks named major theorem surfaces for non-placeholder statements and required anchors. |
| `scripts/audit_bridge_coherence.py` | Checks analytic / physical bridge files for expected imports, ready surfaces, anchors, and boundary markers. |
| `scripts/replay_summary.py` | Generates the replay summary surface. |
| `scripts/check.sh` | Runs the combined local replay path. |

## Core audit-facing documents

| File | Role |
|---|---|
| `README.md` | Public repository overview and boundary statement. |
| `INDEPENDENT_REPLAY.md` | Fresh clone replay procedure. |
| `THEOREM_INDEX.md` | Theorem and bridge surface map. |
| `PHYSICAL_REALIZATION_BOUNDARY.md` | Physical interpretation boundary for singleton / prototype / skeleton surfaces. |
| `EXTERNAL_REVIEW_CHECKLIST.md` | Ordered external review checklist. |
| `EXTERNAL_AUDIT_PACKET.md` | This top-level packet index. |

## Main Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

## Major theorem audit surfaces

The major theorem non-placeholder audit currently covers 12 theorem surfaces:

```text
exact_gap_theorem_body_closure_value
exact_gap_theorem_body_closure_positive
exact_gap_theorem_body_closure_weight_positive
exact_gap_theorem_body_closure_weight_equals_pvm_mass
operator_measure_compatibility_weight_equals_pvm_mass
operator_measure_compatibility_positive_weight
physical_hamiltonian_normalized_gap_def
physical_hamiltonian_gap_reconstruction
physical_hamiltonian_normalized_gap_eq_3320
exact_value_origin_from_theorem_body
exact_value_origin_not_packaging_artifact
exact_value_origin_not_ci_ledger_artifact
```

See `THEOREM_INDEX.md` for file locations and review roles.

## Bridge coherence surfaces

The bridge-coherence audit currently covers 7 bridge files:

```text
MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean
MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean
MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
```

See `THEOREM_INDEX.md` and `PHYSICAL_REALIZATION_BOUNDARY.md` before interpreting these surfaces physically.

## Physical normalization boundary

The normalized theorem-body value is dimensionless:

```text
exactGapValueReal = 33 / 20
```

The physical Hamiltonian normalization uses an explicit reference energy scale:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

Internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
```

Dimensional reading requires an external reference scale:

```text
physicalGap_dimensional = E0 * (33/20)
```

## Physical realization boundary

Singleton / `PUnit` / prototype / skeleton surfaces are:

```text
contract witness surfaces
review surfaces
bridge surfaces
skeleton / prototype closures
boundary-preserving Lean artifacts
```

They are not:

```text
a full continuum Yang-Mills construction
a replacement for the physical Hilbert space
a claim that the physical Hamiltonian is literally one-point
a public final theorem acceptance claim
```

See `PHYSICAL_REALIZATION_BOUNDARY.md` for the full statement.

## Documentation ledgers to compare

Reviewers should compare source files with documentation ledgers including:

```text
docs/mathlib_major_theorem_nonplaceholder_audit.md
docs/mathlib_major_theorem_nonplaceholder_audit_ci.md
docs/mathlib_bridge_coherence_audit.md
docs/mathlib_bridge_coherence_ci.md
docs/mathlib_physical_hamiltonian_normalization_bridge.md
docs/mathlib_physical_hamiltonian_normalization_bridge_ci.md
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
docs/mathlib_concrete_residual_closure.md
docs/mathlib_concrete_residual_closure_ci.md
```

## Successful packet review means

```text
the repository can be replayed from a fresh clone
the pinned Lean toolchain is visible
the audit scripts pass
the Lean build passes
the full local check CI mirrors the reviewer command
the major theorem surfaces are present
the bridge surfaces are present
boundary markers are visible
normalization is not confused with a dimensional physical mass without E0
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
Clay-style final theorem status has been reached
```

## Reviewer record template

```text
Repository: itakura-hidetoshi/4d-mass-gap
Commit SHA reviewed:
Date reviewed:
Lean version:
Lake version:
scripts/check.sh result:
Full Local Check CI result:
lake build result:
Major theorem audit result:
Bridge coherence audit result:
Physical boundary interpretation preserved: yes/no
Normalization boundary preserved: yes/no
Reviewer notes:
```
