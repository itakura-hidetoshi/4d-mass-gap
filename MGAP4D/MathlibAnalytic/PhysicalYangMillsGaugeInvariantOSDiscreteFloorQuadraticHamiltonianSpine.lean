import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDiscreteFloorHamiltonianSpine
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDiscreteFloorQuadraticSelfAdjointness

/-!
# Discrete-floor quadratic OS Hamiltonian spine

This aggregate exposes the route

```text
exact finite integer temporal translations
→ floor dense-time approximation
→ joint continuity
→ continuum Euclidean-time action
→ continuum reflection/time exchange
→ scalar OS quadratic continuity at time zero
→ strong continuity on represented observable states
→ strongly continuous completed OS semigroup
→ graph-closed self-adjoint OS Hamiltonian.
```

The scalar continuity input is the continuity of the reflected OS quadratic
expectation of the translated observable difference.  Hilbert-valued strong
continuity is generated from that scalar input rather than assumed separately.
-/
