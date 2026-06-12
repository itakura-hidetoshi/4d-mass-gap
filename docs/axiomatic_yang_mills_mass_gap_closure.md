# Axiomatic Yang--Mills Mass Gap Closure Route

This note records the conditional proof kernel installed in
`MGAP4D/MathlibAnalytic/AxiomaticYangMillsMassGapClosure.lean`.

## Scope

The file does **not** claim an unconditional solution of the Clay Yang--Mills
mass gap problem.  Instead, it replaces terminal `True` / bare `Prop` /
`ready` / `receipt` markers with explicit theorem projections over displayed
Mathlib data:

- Wightman / Osterwalder--Schrader axiom package,
- gauge group and field-configuration carriers,
- reconstructed Hilbert-space carrier,
- Hamiltonian,
- vacuum,
- spectral PVM interface,
- energy spectrum and energy-momentum spectrum,
- positive-energy condition,
- isolated vacuum,
- positive first non-vacuum spectral excitation.

## Closure theorem

The public theorem is:

```lean
theorem wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    M.hasMassGap ∧ 0 < M.massGapValue ∧
      M.massGapValue = sInf (M.energySpectrum \ ({0} : Set ℝ))
```

Thus, once a concrete four-dimensional Yang--Mills construction supplies the
OS/Wightman readiness assumptions and the reconstructed spectral data, the
mass-gap statement is obtained as an ordinary Lean theorem over the Mathlib
carrier.

## Boundary

The remaining hard part is the construction of such a concrete model from
Yang--Mills theory.  This file is the theorem-level closure target into which
that construction should plug; it is not a substitute for the construction.
