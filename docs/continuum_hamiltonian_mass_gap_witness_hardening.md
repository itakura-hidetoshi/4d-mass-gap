# Continuum Hamiltonian Mass-Gap Witness Hardening

This document records the additive hardening surface introduced in
`MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean`.

The purpose of the layer is to keep the existing
`ContinuumHamiltonianMassGapWitnessData` object installed, while exposing its
principal witness path through upstream theorem-derived witnesses rather than
leaving the continuum-Hamiltonian mass-gap bridge as only an installed review
surface.

## Scope

The hardening surface is internal to the MGAP4D Lean development.  It does not
claim external mathematical consensus and does not replace the external audit
boundary.  It is a theorem-witness bridge over already installed surfaces.

## Required upstream lanes

The hardening bundle explicitly depends on:

- `continuumYangMillsLaneHardeningData.ready`
- `plaquetteSpectralWeightLaneHardeningData.ready`
- `continuumHamiltonianMassGapWitnessData.ready`
- `exactGapValueReal = (33 : ℝ) / 20`
- `0 < exactGapValueReal`

## Theorem-derived witness anchors

The bundle exposes the following theorem-derived anchors:

- `continuum_hamiltonian_mass_gap_witness_hardened_bundle`
- `continuum_hamiltonian_physical_witness_from_hardened_bundle`
- `continuum_hamiltonian_hphys_from_ym_witness_from_hardened_bundle`
- `continuum_hamiltonian_exact_positive_mass_gap_from_hardened_bundle`
- `continuum_hamiltonian_installed_witness_ready_from_hardened_bundle`

The final continuum-Hamiltonian theorem surface is threaded through the bundle
by:

- `continuum_hamiltonian_theorem_uses_hardened_witness_bundle`

## Boundary discipline

The surface remains additive-only.  It does not weaken:

- public theorem-release boundary
- final-release boundary
- external audit boundary
- no-external-consensus boundary

## Interpretation

The hardening should be read as:

> the installed continuum-Hamiltonian witness can now be cited together with
> upstream theorem witnesses from the continuum Yang--Mills hardening lane and
> the plaquette spectral-weight lane.

This is a stronger internal replay surface, not a replacement for independent
external verification.