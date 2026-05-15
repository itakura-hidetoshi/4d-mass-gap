# Mathlib major theorem non-placeholder audit

Branch: main

This note records the additional CI audit that checks major theorem surfaces are not dependent on `axiom`, `sorry`, `admit`, `constant`, or trivial `True`-only theorem statements.

## Added script

```text
scripts/audit_major_theorem_nonplaceholder.py
```

## CI integration

```text
.github/workflows/lean-direct-elan.yml
```

Added audit step:

```text
Audit major theorem non-placeholder surface
python3 scripts/audit_major_theorem_nonplaceholder.py
```

## Existing forbidden-token guard

The existing CI guard already rejects the following Lean tokens after removing comments and strings:

```text
sorry
admit
axiom
constant
```

Implemented in:

```text
scripts/audit_lean_forbidden_tokens.py
```

## Additional non-placeholder audit

The new audit checks the named load-bearing theorem surfaces for:

```text
not merely theorem ... : True :=
not merely : Prop := True
contains exact value / positivity / spectralWeight / PVM mass / normalization anchors
```

## Major theorem surfaces currently audited

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

## Required anchors

The audited statements must contain domain-specific anchors such as:

```text
exactGapValueReal
(33 : ℝ) / 20
0 <
spectralWeight
projectionMass
constructedObservable
exactAtom
normalizedGap
physicalGap
referenceEnergyScale
notPackagingArtifact
notCILedgerArtifact
```

## Meaning

```text
major theorem surfaces are checked against axiom/sorry/admit/constant
major theorem surfaces are checked against trivial True-only statements
33/20 theorem-body origin is checked as a non-placeholder statement
operator-measure/PVM compatibility is checked as a non-placeholder statement
Hamiltonian normalization bridge is checked as a non-placeholder statement
```

## Boundary

```text
this is a syntactic CI audit, not a replacement for Lean kernel checking
Lean kernel checking remains lake build
this audit complements, but does not replace, theorem-body proof review
```
