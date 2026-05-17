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
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build
```

The reviewed job reported:

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

The checkpoint reached these final surfaces under the standard check route:

```text
MGAP4D.MathlibAnalytic.ExactGapReal
MGAP4D.MathlibAnalytic.ExactGapAnalyticRealClosure
MGAP4D.MathlibAnalytic.ExactGapFullInterfaceClosure
MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure
MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin
MGAP4D.MathlibAnalytic.InfiniteDimensionalResidualFillingBridge
MGAP4D.MathlibAnalytic.HardPhysicalResidualHardeningMap
MGAP4D.MathlibAnalytic.HilbertConstructionLaneHardening
MGAP4D.MathlibAnalytic.SelfAdjointHPhysLaneHardening
MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening
MGAP4D.MathlibAnalytic.PlaquetteSpectralWeightLaneHardening
MGAP4D.MathlibAnalytic.FourLaneResidualClosure
MGAP4D.MathlibAnalytic.InternalReviewResidualClosureGate
MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## Named readiness theorem route

The final gate is exposed through named Lean theorem witnesses including:

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

## Exact value preservation route

The exact normalized value remains exposed as:

```text
exactGapValueReal = (33 : ℝ) / 20
```

and is carried into the external-audit-readiness gate through:

```text
external_audit_readiness_exact_value_preserved_witness
external_audit_readiness_exact_value_preserved
```

## Spectral 33/20 replay addendum

The spectral route is now exposed through the complete Hamiltonian derivation,
release-adoption surface, and external-audit gate.

Core spectral theorem surface:

```text
MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
yang_mills_hamiltonian_spectral_infimum_eq_3320
yang_mills_hamiltonian_spectral_attainment_eq_3320
yang_mills_hamiltonian_observable_atom_eq_3320
yang_mills_hamiltonian_spectral_analysis_derives_3320
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_spectral_derivation_exact_gap_value
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
external_audit_readiness_pvm_spectral_atom_value_eq_3320
external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass
external_audit_readiness_pvm_spectral_atom_boundary_held
```

The PVM / observable spectral atom replay receipt records:

```text
observable spectral atom = 33/20
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
  -> spectral infimum = 33/20
  -> spectral attainment = 33/20
  -> observable spectral atom = 33/20
  -> positive nonzero spectral mass
  -> PVM / observable spectral atom public audit projection
  -> exactGapValueReal = 33/20
  -> external-audit-visible spectral addendum
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

The current spectral replay addendum was established after the following PR chain:

```text
PR #49: Derive 33/20 from Yang-Mills Hamiltonian spectral analysis
PR #50: Adopt spectral 33/20 route in complete Hamiltonian release surface
PR #51: Expose spectral 33/20 route at external audit gate
PR #52: Add spectral 33/20 replay certificate route
```

Latest spectral external-audit merge commit:

```text
acfeb8b26a184ee84287c2f5ad5a3139ed74c9e8
```

## Boundary interpretation

This certificate means:

```text
repository-internal Lean replay succeeded
repository-internal audit scripts passed
external-audit-readiness gate built successfully
forbidden Lean tokens were absent in the scanned Lean files
exact normalized value surface was preserved through the gate
spectral infimum / attainment / observable-atom replay route is externally visible
PVM / observable spectral atom positive mass is public-audit-visible
```

This certificate does not mean:

```text
external audit completed
external mathematical consensus obtained
final theorem release opened
future residuals impossible
public theorem boundary removed
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