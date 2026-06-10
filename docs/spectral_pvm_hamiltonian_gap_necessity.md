# Spectral theorem / PVM / Hamiltonian gap necessity

Lean source:

```text
MGAP4D/MathlibAnalytic/SpectralPVMHamiltonianGapNecessity.lean
```

This surface records the exact-gap value as forced by the composed internal route:

```text
continuum Yang--Mills Hamiltonian
  -> H_phys from Yang--Mills
  -> self-adjoint / spectral theorem chain
  -> Rayleigh infimum alignment
  -> Rayleigh attainment alignment
  -> PVM / observable spectral atom alignment
  -> exactGapValueReal = derived Hamiltonian spectral value
  -> chain-index exact 33/20 addendum
  -> derived Hamiltonian spectral value = 33/20
  -> spectral infimum / attainment / observable atom = 33/20
```

Core necessity anchors:

```text
SpectralPVMHamiltonianGapNecessity
spectral_pvm_hamiltonian_gap_necessity_ready
spectral_pvm_hamiltonian_derived_value_eq_33_over_20
spectral_pvm_hamiltonian_infimum_value_eq_33_over_20
spectral_pvm_hamiltonian_attained_value_eq_33_over_20
spectral_pvm_hamiltonian_observable_atom_eq_33_over_20
spectral_pvm_hamiltonian_positive_nonzero_mass
spectral_pvm_hamiltonian_boundary_held
```

Required imported route anchors:

```text
yang_mills_hamiltonian_exact_gap_eq_spectral_value
physical_continuum_hamiltonian_exact_gap_33_over_20
external_audit_readiness_pvm_spectral_atom_public_audit_projection
external_audit_readiness_continuum_hamiltonian_chain_index_addendum_ready
```

Meaning:

```text
the 33/20 value is not pasted as a terminal label;
it is obtained by composing the Hamiltonian spectral value with the exact normalized carrier;
the PVM / observable spectral atom inherits the same value;
positive nonzero spectral mass remains visible;
publicBoundaryHeld and finalReleaseHeld remain held;
external mathematical consensus is not claimed.
```
