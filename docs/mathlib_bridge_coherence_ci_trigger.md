# Mathlib bridge coherence CI trigger

This marker exists to trigger GitHub Actions after adding the dedicated Bridge Coherence CI workflow.

## Target workflow

```text
.github/workflows/bridge-coherence-ci.yml
```

## Target audit script

```text
scripts/audit_bridge_coherence.py
```

## Expected checks

```text
Check Lean forbidden tokens
Check major theorem non-placeholder surface
Check analytic bridge coherence
Summarize Lean replay surface
```

## Bridge coherence scope

```text
Concrete Hilbert realization
Concrete H_phys / unbounded-operator realization
Physical unbounded-operator skeleton
Concrete Yang-Mills Hamiltonian skeleton
Spectral realization skeleton
Continuum spectral theorem skeleton
Physical Hamiltonian normalization bridge
```

## Purpose

```text
trigger push-based Bridge Coherence CI
confirm bridge order
confirm ready surfaces
confirm exact value preservation
confirm normalization bridge
confirm public boundary markers
```
