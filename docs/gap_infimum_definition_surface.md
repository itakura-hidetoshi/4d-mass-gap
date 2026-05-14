# Gap infimum definition surface

This note records the third residual-resolution layer after exact-gap release-readiness.

## Lean artifacts

```text
MGAP4D/Spectral/GapInfimumDefinition.lean
MGAP4D/Spectral.lean
MGAP4D.lean
```

## Added surface

```text
GapInfimumDefinitionTarget
GapInfimumDefinitionSurface
GapInfimumDefinitionSurface.ready
gapInfimum3320DefinitionSurface
gap_infimum_definition_surface_pack
gap_infimum_3320_definition_surface_ready
gap_infimum_3320_definition_exact_value
gap_infimum_3320_definition_hamiltonian_is_Hphys
gap_infimum_3320_definition_release_held
gap_infimum_3320_definition_public_boundary_locked
gap_infimum_3320_definition_no_auto_release
gap_infimum_3320_orthogonal_sector_carrier_surface
gap_infimum_3320_normalized_state_predicate_surface
gap_infimum_3320_rayleigh_functional_surface
gap_infimum_3320_spectral_infimum_surface
gap_infimum_3320_infimum_equals_exact_gap_surface
gap_infimum_3320_lower_bound_compatibility_surface
gap_infimum_3320_eigen_witness_attainment_compatibility_surface
```

## Meaning

The layer exposes the gap-infimum definition obligations needed to connect the exact value to the orthogonal-sector infimum definition.

```text
H_phys operator body ready
exact gap theorem ready
orthogonal sector carrier surface visible
normalized state predicate surface visible
Rayleigh functional surface visible
spectral infimum surface visible
infimum equals exact gap surface visible
lower-bound compatibility surface visible
eigen-witness attainment compatibility surface visible
exact gap value = 33/20
Hamiltonian = H_phys
final release held
public boundary locked
no automatic final release
```

## Gap-infimum targets

```text
orthogonalSectorCarrier
normalizedStatePredicate
rayleighFunctionalSurface
spectralInfimumSurface
infimumEqualsExactGap
lowerBoundCompatibility
eigenWitnessAttainmentCompatibility
```

## Boundary

```text
pre-Mathlib gap-infimum definition surface only
third residual-resolution target visible
analytic infimum theorem body not yet replaced
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
