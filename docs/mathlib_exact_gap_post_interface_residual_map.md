# Mathlib exact-gap post-interface residual map

Branch: main

This note records the residual map after the Mathlib exact-gap full interface closure.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/ExactGapPostInterfaceResidualMap.lean
MGAP4D/MathlibAnalytic.lean
```

## Added residual map

```text
MathlibAnalytic.ExactGapPostInterfaceResidualMap
MathlibAnalytic.ExactGapPostInterfaceResidualMap.ready
MathlibAnalytic.exactGapPostInterfaceResidualMap
MathlibAnalytic.exact_gap_post_interface_residual_map_ready
MathlibAnalytic.exact_gap_post_interface_hilbert_rayleigh_open
MathlibAnalytic.exact_gap_post_interface_self_adjoint_hphys_open
MathlibAnalytic.exact_gap_post_interface_spectral_theorem_open
MathlibAnalytic.exact_gap_post_interface_pvm_open
MathlibAnalytic.exact_gap_post_interface_observable_atom_open
MathlibAnalytic.exact_gap_post_interface_no_final_release_from_interface_only
MathlibAnalytic.exact_gap_post_interface_public_boundary_held
```

The historical theorem names are retained for compatibility, but their payloads
are no longer `True`/`trivial` placeholders.  They now project concrete facts
from the interface chain.

## Typed post-interface facts

```text
exactGapValueReal ∈ exactGapEnergyRay
exactGapValueReal ∈ Set.Ioi (0 : ℝ)
exactGapValueReal ∈ Set.Ioi (1 : ℝ)
singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal
singletonObservableAtomInterface.atom = exactGapAtomReal
observable atom spectral weight is positive
observable atom spectral weight is nonzero
observable atom spectral weight lies in Set.Ioi (0 : ℝ)
observable atom spectral weight equals the PVM projection mass at the exact atom
```

## Remaining non-interface theorem bodies

```text
full Hilbert-space Rayleigh quotient theorem
full unbounded self-adjoint H_phys theorem
full spectral theorem integration
full projection-valued-measure theorem
full observable atom theorem in operator-measure form
compactly supported smeared centered plaquette construction theorem
operator-measure compatibility theorem
```

## Meaning

```text
full interface closure is ready
post-interface slots now expose concrete typed facts
no True/trivial residual witness is used in this map
interface closure alone is not treated as external mathematical consensus
public theorem boundary remains held by positive observable weight
```

## Boundary

```text
residual map only
not external consensus
not Clay-style public acceptance
next step should choose one residual theorem body to close or harden
```
