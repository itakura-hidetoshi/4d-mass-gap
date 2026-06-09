# External audit readiness replay certificate

This document records a compact replay certificate for the current external-audit-readiness checkpoint.

It is intended to help an independent reviewer locate the repository-internal evidence chain without interpreting CI success as external mathematical consensus.

This file is documentation-only. It does not modify Lean semantics. It does not open final theorem release. It does not claim independent external mathematical consensus.

## Checkpoint identity

```text
Repository: itakura-hidetoshi/4d-mass-gap
Checkpoint commit: de76fd42f0e5c3bfd58090bfb2eef2510f6b5d63
Workflow run: 25973699153
Workflow job: 76350067649
Job name: Run scripts/check.sh
Result: success
```

## Replay route

The reviewed checkpoint used the repository's standard replay command:

```bash
bash scripts/check.sh
```

The script route includes the following final Lean build targets:

```bash
lake build MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build
```

The historical reviewed job reported:

```text
Build completed successfully (8368 jobs).
[check] lake build
Build completed successfully (0 jobs).
```

## Lean audit summary at checkpoint

```text
Lean files scanned: 457
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 8
```

The replay summary emitted by the script route reported:

```text
lean_files: 457
imports: 1191
declaration_like_lines: 2663
namespace_lines: 938
total_lines: 27611
```

## Final gate surfaces reached by the replay

```text
MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## Named readiness theorem route

```text
external_audit_readiness_internal_gate_ready_witness
external_audit_readiness_bundle_manifest_ready_witness
external_audit_readiness_chain_index_ready_witness
external_audit_readiness_repository_internal_residual_closed_witness
external_audit_readiness_no_review_level_residual_left_witness
external_audit_readiness_independent_replay_visible_witness
external_audit_readiness_audit_script_route_visible_witness
external_audit_readiness_ci_route_visible_witness
external_audit_readiness_external_audit_ready_witness
external_audit_readiness_external_consensus_not_claimed_witness
external_audit_readiness_public_boundary_held_witness
external_audit_readiness_final_release_held_witness
external_audit_readiness_exact_value_preserved_witness
external_audit_readiness_gate_ready
```

## Abstract exact-value carrier route

The external-audit gate now preserves the carrier abstractly:

```text
external_audit_readiness_exact_value_preserved_witness
external_audit_readiness_exact_value_preserved
exactGapValueReal = exactGapValueReal
```

It does not assert a pre-R6 `33/20` derivation.

## Spectral value alignment replay addendum

The spectral route is now exposed through the complete Hamiltonian derivation,
release-adoption surface, and external-audit gate as value alignment before R6.

Core spectral theorem surface:

```text
MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
yang_mills_hamiltonian_spectral_infimum_eq_derived
yang_mills_hamiltonian_spectral_attainment_eq_derived
yang_mills_hamiltonian_observable_atom_eq_derived
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_spectral_derivation_positive_mass
yang_mills_hamiltonian_spectral_derivation_nonzero_mass
```

Complete Hamiltonian spectral replay surface:

```text
Physical4DYMContinuumHamiltonianSpectralCompleteDerivationReady
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
```

Complete spectral release-adoption replay surface:

```text
continuumHamiltonianCompleteSpectralMassGapReleaseAdoptionReady
continuum_hamiltonian_complete_spectral_mass_gap_release_adoption_ready
continuum_hamiltonian_complete_spectral_release_adoption_exact_mass_gap
continuum_hamiltonian_complete_spectral_release_adoption_positive_nonzero_mass
continuum_hamiltonian_complete_spectral_release_adoption_boundary_preserved
```

External-audit spectral replay surface:

```text
externalAuditReadinessCompleteSpectralMassGapAddendumReady
external_audit_readiness_complete_spectral_mass_gap_addendum_ready
external_audit_readiness_complete_spectral_mass_gap_exact_value
external_audit_readiness_complete_spectral_mass_gap_positive_nonzero_mass
external_audit_readiness_complete_spectral_mass_gap_boundary_held
```

## PVM / observable spectral atom replay receipt

The PVM / observable spectral atom route is now exposed as a public-audit projection:

```text
externalAuditReadinessPVMSpectralAtomPublicAuditProjection
external_audit_readiness_pvm_spectral_atom_public_audit_projection
external_audit_readiness_pvm_spectral_atom_value_eq_derived
external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass
external_audit_readiness_pvm_spectral_atom_boundary_held
```

The PVM / observable spectral atom replay receipt records:

```text
observable spectral atom = derived Hamiltonian spectral value
PVM spectral mass > 0
PVM spectral mass != 0
publicBoundaryHeld
finalReleaseHeld
```

The replay meaning is:

```text
Yang--Mills continuum Hamiltonian
  -> self-adjoint / spectral chain
  -> Rayleigh lower bound
  -> Rayleigh attainment
  -> spectral infimum = derived Hamiltonian spectral value
  -> spectral attainment = derived Hamiltonian spectral value
  -> observable spectral atom = derived Hamiltonian spectral value
  -> positive nonzero spectral mass
  -> PVM / observable spectral atom public audit projection
  -> exactGapValueReal = derived Hamiltonian spectral value
  -> external-audit-visible spectral alignment addendum
  -> no upstream 33/20 claim
```

The spectral replay route is checked by:

```text
python3 scripts/audit_yang_mills_hamiltonian_spectral_derivation_3320.py
python3 scripts/audit_external_audit_readiness_gate.py
python3 scripts/audit_external_audit_readiness_replay_certificate.py
lake build MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## Boundary interpretation

This certificate means:

```text
repository-internal Lean replay succeeded
repository-internal audit scripts passed
external-audit-readiness gate built successfully
forbidden Lean tokens were absent in the scanned Lean files
abstract exact-value carrier was preserved through the gate
spectral infimum / attainment / observable-atom alignment route is externally visible
PVM / observable spectral atom positive mass is public-audit-visible
```

This certificate does not mean:

```text
external audit completed
external mathematical consensus obtained
final theorem release opened
future residuals impossible
public theorem boundary removed
33/20 was derived upstream of R6
```

## Reviewer checklist

A reviewer can independently replay the current route by checking:

```text
1. lean --version reports Lean 4.30.0-rc2 or a declared compatible toolchain.
2. lake --version reports the matching Lake version.
3. bash scripts/check.sh completes.
4. lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate completes.
5. lake build completes.
6. scripts/audit_lean_forbidden_tokens.py reports sorry/admit/axiom/constant all zero.
7. scripts/audit_external_audit_readiness_gate.py passes.
8. scripts/audit_external_audit_readiness_gate_field_classification.py passes.
9. scripts/audit_yang_mills_hamiltonian_spectral_derivation_3320.py passes.
10. scripts/audit_external_audit_readiness_replay_certificate.py passes.
11. lake build MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320 completes.
12. lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption completes.
13. external_audit_readiness_pvm_spectral_atom_public_audit_projection is present.
14. external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass is present.
```

## Status

```text
Status: replay-certificate prepared
Semantic effect: documentation-only
Lean semantics changed: no
External consensus claimed: no
External audit completed: no
Final theorem release opened: no
Spectral replay addendum visible: yes
PVM spectral atom public audit projection visible: yes
```
