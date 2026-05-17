# External audit theorem witness index certificate

This document records the additive theorem-witness index introduced for the continuum-Hamiltonian mass-gap surface.

It is intended to help an external reviewer trace the repository-internal theorem witnesses without interpreting repository replay success as external mathematical consensus.

This file is documentation-only. It does not modify Lean semantics. It does not replace the existing external-audit-readiness gate. It does not open final theorem release. It does not claim independent external mathematical consensus.

## Checkpoint identity

```text
Repository: itakura-hidetoshi/4d-mass-gap
Pull request: 20
Workflow run: 25978245953
Workflow job: 76362202736
Merge checkpoint: 15379002b160c944f311e2013b8b8d1d174d6c67
Head checkpoint: 89c97b8ca3a770a0525ea16591f21951fd1828e2
Job name: Run scripts/check.sh
Result: success
```

## Replay route

The reviewed checkpoint used the repository's standard replay command:

```bash
bash scripts/check.sh
```

The script route includes the theorem witness index audit and final Lean build target:

```bash
python3 scripts/audit_external_audit_theorem_witness_index.py
lake build MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex
lake build
```

The reviewed job reported:

```text
Build completed successfully (8372 jobs).
[check] lake build
Build completed successfully (0 jobs).
```

## Lean audit summary at checkpoint

```text
Lean files scanned: 461
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 8
```

The replay summary emitted by the script route reported:

```text
lean_files: 461
imports: 1203
declaration_like_lines: 2697
namespace_lines: 946
total_lines: 28031
```

## Theorem witness index surface

The index is exposed by:

```text
MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex
ExternalAuditTheoremWitnessIndexData
externalAuditTheoremWitnessIndexData
external_audit_theorem_witness_index_ready
```

The index intentionally gathers these witness components:

```text
externalAuditReadinessGateData.ready
finalTheoremReleaseBundleManifestReviewSurface.ready
continuumHamiltonianMassGapWitnessData.ready
0 < exactGapValueReal
exactGapValueReal = (33 : ℝ) / 20
continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady
continuumHamiltonianMassGapWitnessData.theoremWitnessOnly
continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim
continuumHamiltonianMassGapWitnessData.publicBoundaryHeld
continuumHamiltonianMassGapWitnessData.finalReleaseHeld
```

## Named witness route

The index exposes the following named Lean theorem witnesses:

```text
external_audit_theorem_witness_index_ready
external_audit_theorem_witness_index_positive_exact_mass_gap
external_audit_theorem_witness_index_chain_ready
external_audit_theorem_witness_index_no_external_consensus_claim
external_audit_theorem_witness_index_boundaries_held
```

These names are intentionally short enough for an external reviewer to grep directly.

## Continuum-Hamiltonian mass-gap witness route

The witness index depends on the additive continuum-Hamiltonian mass-gap witness chain:

```text
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitness
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption
continuumHamiltonianMassGapWitnessData.ready
continuum_hamiltonian_mass_gap_witness_ready
continuum_hamiltonian_mass_gap_theorem_ready
continuum_hamiltonian_mass_gap_release_adoption_ready
continuum_hamiltonian_derives_mass_gap_chain
```

## Boundary interpretation

This certificate means:

```text
repository-internal Lean replay succeeded
repository-internal audit scripts passed
the external-audit theorem witness index built successfully
the exact normalized value surface was preserved into the index
the continuum-Hamiltonian-to-mass-gap witness chain is visible
public/final-release boundaries remain visible
```

This certificate does not mean:

```text
external audit completed
external mathematical consensus obtained
final theorem release opened
future residuals impossible
public theorem boundary removed
Clay problem accepted as solved
```

## Reviewer checklist

A reviewer can independently replay the current route by checking:

```text
1. lean --version reports Lean 4.30.0-rc2 or a declared compatible toolchain.
2. lake --version reports the matching Lake version.
3. bash scripts/check.sh completes.
4. scripts/audit_external_audit_theorem_witness_index.py passes.
5. lake build MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex completes.
6. lake build completes.
7. scripts/audit_lean_forbidden_tokens.py reports sorry/admit/axiom/constant all zero.
8. the named theorem witnesses above appear in MGAP4D/MathlibAnalytic/ExternalAuditTheoremWitnessIndex.lean.
```

## Status

```text
Status: theorem-witness-index certificate prepared
Semantic effect: documentation-only
Lean semantics changed: no
External consensus claimed: no
External audit completed: no
Final theorem release opened: no
```