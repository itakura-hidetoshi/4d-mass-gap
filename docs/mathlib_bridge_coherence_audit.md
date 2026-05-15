# Mathlib bridge coherence audit

Branch: main

This note records the bridge-coherence audit for the analytic/physical theorem chain.

## Added script

```text
scripts/audit_bridge_coherence.py
```

## Added workflow

```text
.github/workflows/bridge-coherence-ci.yml
```

Workflow name:

```text
Bridge Coherence CI
```

## Audited bridge chain

```text
Concrete Hilbert realization
  -> Concrete H_phys / unbounded-operator realization
  -> Physical unbounded-operator skeleton
  -> Concrete Yang-Mills Hamiltonian skeleton
  -> Spectral realization skeleton
  -> Continuum spectral theorem skeleton
  -> Physical Hamiltonian normalization bridge
```

## Ordered import edges audited

```text
ConcreteHPhysRealizationTheorem imports ConcreteHilbertRealizationTheorem
ConcreteYangMillsHamiltonianSkeleton imports PhysicalUnboundedOperatorSkeleton
SpectralRealizationSkeleton imports ConcreteYangMillsHamiltonianSkeleton
ContinuumSpectralTheoremSkeleton imports SpectralRealizationSkeleton
```

## Required coherence anchors

The audit checks that the bridge files expose anchors for:

```text
Hilbert distinguished nonzero norm
Rayleigh lower bound
Rayleigh exact attainment
H_phys domain preservation
H_phys symmetry on domain
mapping into abstract H_phys domain
Yang-Mills data and witness
coupling positivity
normalization positivity
H_phys built from Yang-Mills data
plaquette centeredness
spectral projection
spectral mass
exact atom presence
observable witness
positive mass at exact value
continuum limit map
continuum spectral projection
continuum spectral mass
continuum spectral theorem certificate
exact atom preservation
positive mass preservation
observable witness preservation
Hamiltonian normalization equations
exact value 33/20
public boundary markers
```

## CI checks

The workflow runs:

```text
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/replay_summary.py
```

## Meaning

```text
bridge order is mechanically audited
ready surfaces are mechanically audited
exact value preservation is mechanically audited
normalization bridge is mechanically audited
public boundary markers are mechanically audited
forbidden Lean proof-gap tokens are rechecked
major theorem non-placeholder audit is rechecked
```

## Boundary

```text
syntactic/contract audit only
not a substitute for Lean kernel checking
not a substitute for external mathematical peer review
complements lake build and theorem-body proof review
public theorem boundary held
```
