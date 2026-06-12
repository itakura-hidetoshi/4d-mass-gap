# External Review Checklist

This checklist gives an external reviewer a short, ordered path through the MGAP4D repository.

It complements:

```text
README.md
EXTERNAL_AUDIT_PACKET.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/axiomatic_yang_mills_mass_gap_closure.md
docs/mathlib_physical_unbounded_operator_skeleton.md
docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/complete_infinite_dimensional_hilbert_construction.md
docs/continuum_hamiltonian_complete_release_surface.md
docs/external_audit_readiness_gate_ci.md
```

It does not replace Lean kernel checking, source inspection, or independent mathematical review.

## 0. Review boundary acknowledgement

Before starting, record that the current repository claim is:

```text
internal normalized theorem-body / proof-architecture surface
with replay, audit, bridge-coherence support, explicit infinite-dimensional Yang-Mills target obligations,
complete infinite-dimensional Hilbert construction, downstream hardening lanes,
final-physical-carrier routing for the physical unbounded-operator and concrete Yang-Mills Hamiltonian skeletons,
continuum-Hamiltonian theorem/release surfaces, OS/Wightman conditional definition bridge, and external-audit readiness gates
```

It is not a claim of:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
a completed public-final continuum Yang-Mills proof solely from CI or audit ledgers
an unconditional construction of the OS/Wightman Yang-Mills bridge
```

Reviewer checkpoint:

```text
[ ] I understand the public final theorem boundary is review-gated.
[ ] I understand CI/audit scripts do not replace mathematical review.
[ ] I understand the normalized value 33/20 is dimensionless unless E0 is supplied.
[ ] I understand the complete Hilbert construction and continuum-Hamiltonian surfaces are repository-internal Lean surfaces pending external audit.
[ ] I understand the current physical unbounded-operator and concrete Yang-Mills Hamiltonian skeletons are routed through `FinalPhysicalHilbertCarrier`, not through a one-point carrier.
[ ] I understand the OS/Wightman mass-gap bridge is conditional on an explicitly supplied bridge object.
```

## 1. Fresh clone

Run:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
```

Reviewer checkpoint:

```text
[ ] Repository cloned from the public GitHub URL.
[ ] No unpublished local files are required.
```

## 2. Toolchain confirmation

Run:

```bash
cat lean-toolchain
lean --version
lake --version
```

Expected pinned toolchain family:

```text
leanprover/lean4:v4.30.0-rc2
Lean 4.30.0-rc2
Lake compatible with the pinned Lean toolchain
```

Reviewer checkpoint:

```text
[ ] `lean-toolchain` is present.
[ ] Lean version matches the pinned toolchain family.
[ ] Lake is available.
```

## 3. One-command replay

Run:

```bash
bash scripts/check.sh
```

Expected stages:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit proof placeholder inventory
[check] audit final physical carrier routing
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit complete infinite-dimensional Hilbert construction
[check] audit self-adjoint HPhys lane hardening
[check] audit continuum Yang-Mills lane hardening
[check] audit plaquette spectral weight lane hardening
[check] audit continuum Hamiltonian witness hardening
[check] audit four-lane residual closure
[check] audit internal review residual closure gate
[check] audit external audit readiness gate
[check] audit external audit readiness gate field classification
[check] audit external audit readiness replay certificate
[check] audit OS/Wightman mass-gap bridge
[check] replay summary
[check] lake update
[check] build continuum Hamiltonian exact mass-gap derivation
[check] build continuum Hamiltonian release-chain addendum
[check] build external audit readiness gate
[check] build OS/Wightman mass-gap external audit bridge
[check] lake build
```

Reviewer checkpoint:

```text
[ ] `scripts/check.sh` exits with status 0.
[ ] Manifest verification passes.
[ ] Forbidden-token audit passes.
[ ] Major theorem non-placeholder audit passes.
[ ] Final physical carrier routing audit passes.
[ ] Bridge-coherence audit passes.
[ ] OS/Wightman mass-gap bridge audit passes.
[ ] Infinite-dimensional target-layer audit passes.
[ ] Complete infinite-dimensional Hilbert construction audit passes.
[ ] Continuum-Hamiltonian exact mass-gap derivation build succeeds.
[ ] External audit readiness gate build succeeds.
[ ] OS/Wightman mass-gap external audit bridge build succeeds.
[ ] Final `lake build` succeeds.
```

## 4. Manual replay, if needed

If `scripts/check.sh` fails or if individual stage inspection is desired, run:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_proof_placeholder_inventory.py
python3 scripts/audit_final_physical_carrier_routing.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/audit_complete_infinite_dimensional_hilbert_construction.py
python3 scripts/audit_self_adjoint_hphys_lane_hardening.py
python3 scripts/audit_continuum_yang_mills_lane_hardening.py
python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py
python3 scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py
python3 scripts/audit_four_lane_residual_closure.py
python3 scripts/audit_internal_review_residual_closure_gate.py
python3 scripts/audit_external_audit_readiness_gate.py
python3 scripts/audit_external_audit_readiness_gate_field_classification.py
python3 scripts/audit_external_audit_readiness_replay_certificate.py
python3 scripts/audit_os_wightman_mass_gap_bridge.py
python3 scripts/replay_summary.py
lake update
lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianExactMassGapDerivation
lake build MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndexContinuumHamiltonianAddendum
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge
lake build
```

Reviewer checkpoint:

```text
[ ] Each audit script has been inspected individually, if needed.
[ ] The first failing stage has been identified, if any.
```

## 5. Inspect major theorem surfaces

Use:

```text
THEOREM_INDEX.md
```

Inspect the 12 major theorem surfaces audited by:

```bash
python3 scripts/audit_major_theorem_nonplaceholder.py
```

Reviewer checkpoint:

```text
[ ] `exact_gap_theorem_body_closure_value` inspected.
[ ] `exact_gap_theorem_body_closure_positive` inspected.
[ ] `exact_gap_theorem_body_closure_weight_positive` inspected.
[ ] `exact_gap_theorem_body_closure_weight_equals_pvm_mass` inspected.
[ ] `operator_measure_compatibility_weight_equals_pvm_mass` inspected.
[ ] `operator_measure_compatibility_positive_weight` inspected.
[ ] `physical_hamiltonian_normalized_gap_def` inspected.
[ ] `physical_hamiltonian_gap_reconstruction` inspected.
[ ] `physical_hamiltonian_normalized_gap_eq_3320` inspected.
[ ] `exact_value_origin_from_theorem_body` inspected.
[ ] `exact_value_origin_not_packaging_artifact` inspected.
[ ] `exact_value_origin_not_ci_ledger_artifact` inspected.
```

## 6. Inspect bridge, target, and complete Hilbert surfaces

Use:

```text
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/axiomatic_yang_mills_mass_gap_closure.md
docs/mathlib_physical_unbounded_operator_skeleton.md
docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/infinite_dimensional_residual_filling_bridge.md
docs/hard_physical_residual_hardening_map.md
docs/complete_infinite_dimensional_hilbert_construction.md
```

Reviewer checkpoint:

```text
[ ] `AxiomaticYangMillsMassGapClosure.lean` inspected for OS/Wightman axiom package and model-level `hasMassGap`.
[ ] `OSWightmanHamiltonianReconstructionSpine.lean` inspected as the conditional reconstruction spine.
[ ] `OSWightmanMassGapDefinitionBridge.lean` inspected as the explicit Hamiltonian/PVM definition bridge.
[ ] `OSWightmanMassGapExternalAuditBridge.lean` inspected as the external-audit projection for the conditional OS/Wightman route.
[ ] `ConcreteHilbertRealizationTheorem.lean` inspected with boundary markers.
[ ] `ConcreteHPhysRealizationTheorem.lean` inspected with boundary markers.
[ ] `PhysicalUnboundedOperatorSkeleton.lean` inspected with boundary markers.
[ ] `PhysicalUnboundedOperatorSkeleton.lean` inspected for `FinalPhysicalHilbertCarrier`, `finalPhysicalHamiltonian`, `finalPhysicalRayleigh`, and `finalPhysicalUnboundedOperatorSkeletonData`.
[ ] `PhysicalUnboundedOperatorSkeleton.lean` inspected to confirm final-name routing without legacy prototype aliases.
[ ] `ConcreteYangMillsHamiltonianSkeleton.lean` inspected with boundary markers.
[ ] `ConcreteYangMillsHamiltonianSkeleton.lean` inspected for `FinalPhysicalHilbertCarrier`, `finalPhysicalHamiltonian`, `finalPhysicalRayleigh`, and `finalConcreteYangMillsHamiltonianSkeletonData`.
[ ] `ConcreteYangMillsHamiltonianSkeleton.lean` inspected to confirm final-name routing without legacy prototype aliases.
[ ] `SpectralRealizationSkeleton.lean` inspected with boundary markers.
[ ] `ContinuumSpectralTheoremSkeleton.lean` inspected with boundary markers.
[ ] `PhysicalHamiltonianNormalizationBridge.lean` inspected with boundary markers.
[ ] `InfiniteDimensionalYangMillsRealizationTargets.lean` inspected as target-obligation layer.
[ ] `CompleteInfiniteDimensionalHilbertConstruction.lean` inspected as the active complete Hilbert construction lane.
[ ] `HilbertToPhysicalUnboundedOperatorBridge.lean` inspected as the bridge from complete Hilbert lane to physical unbounded operator lane.
```

## 7. Inspect continuum-Hamiltonian route

Use:

```text
docs/continuum_hamiltonian_mass_gap_witness_hardening.md
docs/continuum_hamiltonian_complete_release_surface.md
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitness.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
```

Reviewer checkpoint:

```text
[ ] Continuum-Hamiltonian witness surface inspected.
[ ] Exact normalized mass-gap derivation surface inspected.
[ ] Complete mass-gap derivation surface inspected.
[ ] Release-adoption and public-boundary markers inspected.
```

## 8. Interpret singleton / prototype / skeleton / target surfaces correctly

Read:

```text
PHYSICAL_REALIZATION_BOUNDARY.md
docs/axiomatic_yang_mills_mass_gap_closure.md
docs/mathlib_physical_unbounded_operator_skeleton.md
docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/complete_infinite_dimensional_hilbert_construction.md
```

Reviewer checkpoint:

```text
[ ] I have not interpreted remaining `PUnit` / singleton surfaces as the final physical Hilbert space.
[ ] I have confirmed that the physical unbounded-operator skeleton is final-physical-carrier routed.
[ ] I have confirmed that the concrete Yang-Mills Hamiltonian skeleton is final-physical-carrier routed.
[ ] I have not interpreted prototype spectral mass as the final physical spectral measure.
[ ] I have checked the relevant `publicBoundaryHeld` / `finalReleaseHeld` markers.
[ ] I have distinguished contract witnesses from physical continuum realization targets.
[ ] I have interpreted the infinite-dimensional target layer and complete Hilbert construction as repository-internal Lean surfaces pending external audit.
[ ] I have interpreted the OS/Wightman bridge as conditional theorem plumbing, not as an unconditional construction of Yang-Mills theory.
```

## 9. Check normalization and dimensional reading

Inspect:

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
```

Confirm the normalization logic:

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

Reviewer checkpoint:

```text
[ ] I understand `33/20` as the dimensionless normalized value.
[ ] I understand dimensional interpretation requires an external reference scale `E0`.
[ ] I have not treated `33/20` alone as a dimensionful physical mass.
```

## 10. Compare source files with documentation ledgers

Relevant ledgers include:

```text
docs/axiomatic_yang_mills_mass_gap_closure.md
docs/mathlib_major_theorem_nonplaceholder_audit.md
docs/mathlib_major_theorem_nonplaceholder_audit_ci.md
docs/mathlib_bridge_coherence_audit.md
docs/mathlib_bridge_coherence_ci.md
docs/mathlib_physical_hamiltonian_normalization_bridge.md
docs/mathlib_physical_hamiltonian_normalization_bridge_ci.md
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
docs/mathlib_physical_unbounded_operator_skeleton.md
docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md
docs/mathlib_concrete_residual_closure.md
docs/mathlib_concrete_residual_closure_ci.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/infinite_dimensional_residual_filling_bridge.md
docs/hard_physical_residual_hardening_map.md
docs/complete_infinite_dimensional_hilbert_construction.md
docs/four_lane_residual_closure.md
docs/internal_review_residual_closure_gate.md
docs/external_audit_readiness_gate.md
docs/external_audit_readiness_gate_field_classification.md
docs/external_audit_readiness_replay_certificate.md
docs/full_local_check_ci.md
```

Reviewer checkpoint:

```text
[ ] Documentation ledgers have been compared against source statements.
[ ] CI ledgers are treated as evidence of replay, not as substitutes for proof review.
```

## 11. Final external-review notes

A successful checklist pass means:

```text
the repository can be independently replayed
the declared theorem surfaces are present
the declared bridge surfaces are present
the conditional OS/Wightman mass-gap definition bridge is present and audited
the infinite-dimensional target obligations are present
the complete infinite-dimensional Hilbert construction is present
the physical unbounded-operator skeleton is final-physical-carrier routed
the concrete Yang-Mills Hamiltonian skeleton is final-physical-carrier routed
the continuum-Hamiltonian theorem and complete release surfaces are present
the audit scripts pass
the Lean build passes
public-boundary markers are visible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
Clay-style final theorem status has been reached
the target / construction / gate layers alone complete external public proof acceptance
the conditional OS/Wightman bridge supplies an unconditional Yang-Mills construction
```

Final reviewer checkpoint:

```text
[ ] Replay result recorded.
[ ] Commit SHA recorded.
[ ] Lean / Lake versions recorded.
[ ] Any failures or concerns recorded with file names and theorem names.
[ ] Final physical carrier routing for the unbounded-operator and concrete Yang-Mills Hamiltonian skeletons recorded.
[ ] OS/Wightman bridge conditionality recorded.
[ ] Infinite-dimensional target-layer interpretation preserved.
[ ] Complete Hilbert construction interpretation preserved.
[ ] Public-boundary interpretation preserved.
```
