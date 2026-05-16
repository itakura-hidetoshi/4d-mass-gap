# External Review Checklist

This checklist gives an external reviewer a short, ordered path through the MGAP4D repository.

It complements:

```text
README.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/infinite_dimensional_yang_mills_target_layer.md
```

It does not replace Lean kernel checking, source inspection, or independent mathematical review.

## 0. Review boundary acknowledgement

Before starting, record that the current repository claim is:

```text
internal normalized theorem-body / proof-architecture surface
with replay, audit, bridge-coherence support, and explicit infinite-dimensional Yang-Mills target obligations
```

It is not a claim of:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
a completed infinite-dimensional continuum Yang-Mills proof solely from the target layer
```

Reviewer checkpoint:

```text
[ ] I understand the public final theorem boundary is review-gated.
[ ] I understand CI/audit scripts do not replace mathematical review.
[ ] I understand the normalized value 33/20 is dimensionless unless E0 is supplied.
[ ] I understand the infinite-dimensional target layer is a proof-obligation surface, not final theorem acceptance.
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
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] replay summary
[check] lake update
[check] lake build
```

Reviewer checkpoint:

```text
[ ] `scripts/check.sh` exits with status 0.
[ ] Manifest verification passes.
[ ] Forbidden-token audit passes.
[ ] Major theorem non-placeholder audit passes.
[ ] Bridge-coherence audit passes.
[ ] Infinite-dimensional target-layer audit passes.
[ ] Replay summary is generated.
[ ] `lake build` succeeds.
```

## 4. Manual replay, if needed

If `scripts/check.sh` fails or if individual stage inspection is desired, run:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/replay_summary.py
lake update
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

## 6. Inspect bridge and target surfaces

Use:

```text
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/infinite_dimensional_yang_mills_target_layer.md
```

Inspect the 8 bridge / target surfaces audited by:

```bash
python3 scripts/audit_bridge_coherence.py
```

Reviewer checkpoint:

```text
[ ] `ConcreteHilbertRealizationTheorem.lean` inspected with boundary markers.
[ ] `ConcreteHPhysRealizationTheorem.lean` inspected with boundary markers.
[ ] `PhysicalUnboundedOperatorSkeleton.lean` inspected with boundary markers.
[ ] `ConcreteYangMillsHamiltonianSkeleton.lean` inspected with boundary markers.
[ ] `SpectralRealizationSkeleton.lean` inspected with boundary markers.
[ ] `ContinuumSpectralTheoremSkeleton.lean` inspected with boundary markers.
[ ] `PhysicalHamiltonianNormalizationBridge.lean` inspected with boundary markers.
[ ] `InfiniteDimensionalYangMillsRealizationTargets.lean` inspected as target-obligation layer.
```

## 7. Interpret singleton / prototype / skeleton / target surfaces correctly

Read:

```text
PHYSICAL_REALIZATION_BOUNDARY.md
docs/infinite_dimensional_yang_mills_target_layer.md
```

Reviewer checkpoint:

```text
[ ] I have not interpreted `PUnit` / singleton surfaces as the final physical Hilbert space.
[ ] I have not interpreted prototype spectral mass as the final physical spectral measure.
[ ] I have checked the relevant `publicBoundaryHeld` / `finalReleaseHeld` markers.
[ ] I have distinguished contract witnesses from physical continuum realization targets.
[ ] I have interpreted the infinite-dimensional target layer as proof obligations, not as completed continuum proof.
```

## 8. Check normalization and dimensional reading

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

## 9. Compare source files with documentation ledgers

Relevant ledgers include:

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
docs/infinite_dimensional_yang_mills_target_layer.md
docs/full_local_check_ci.md
```

Reviewer checkpoint:

```text
[ ] Documentation ledgers have been compared against source statements.
[ ] CI ledgers are treated as evidence of replay, not as substitutes for proof review.
```

## 10. Final external-review notes

A successful checklist pass means:

```text
the repository can be independently replayed
the declared theorem surfaces are present
the declared bridge surfaces are present
the infinite-dimensional target obligations are present
the audit scripts pass
the Lean build passes
public-boundary markers are visible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
Clay-style final theorem status has been reached
the target layer alone completes the physical continuum proof
```

Final reviewer checkpoint:

```text
[ ] Replay result recorded.
[ ] Commit SHA recorded.
[ ] Lean / Lake versions recorded.
[ ] Any failures or concerns recorded with file names and theorem names.
[ ] Infinite-dimensional target-layer interpretation preserved.
[ ] Public-boundary interpretation preserved.
```
