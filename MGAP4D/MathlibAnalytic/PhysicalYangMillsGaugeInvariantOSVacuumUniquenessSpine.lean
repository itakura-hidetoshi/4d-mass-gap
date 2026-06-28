import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSHamiltonianSpine
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumUniqueness

/-!
# Physical gauge-invariant OS vacuum-uniqueness spine

This aggregate extends the physical OS Hamiltonian construction by the
conditional zero-energy classification obtained from the transferred positive
vacuum-sector gap:

```text
finite-volume vacuum-gap transfer
→ closed OS Hamiltonian Rayleigh lower bound on the vacuum-orthogonal sector
→ orthogonalization of an arbitrary zero-energy domain vector
→ vanishing of its excitation component
→ zero-energy eigenspace equals the normalized vacuum line
```

For every vector `psi` in the graph-closed Hamiltonian domain, Mathlib proves

```text
H psi = 0 ↔ psi = ⟪psi, Ω⟫ Ω.
```

The result is conditional on the existing `FiniteVolumeVacuumGapTransfer`
package and does not construct that physical transfer input by itself.
-/
