import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingCenteredQuadraticLimit

/-!
# Concrete finite Wilson OS gap frontier

This aggregate exposes the theorem-generated route

```text
finite periodic SU(N) Wilson reflected-integral decay
→ half-time OS quadratic decay
→ centered quadratic-value weak-star convergence
→ continuum centered observable-core decay
→ completed continuum vacuum-sector semigroup decay
→ positive right-Hamiltonian Rayleigh lower bound
```

Finite OS contractivity and reflection/time exchange also pass through weak-star
limits, generating the continuum contraction semigroup and its inner-product
symmetry.

No isometric embeddings of the finite OS Hilbert spaces into a common Hilbert
carrier are needed for this route.

The remaining model-specific inputs are the common positive-time translation,
a scale-uniform strict reflected-integral decay with positive slope, and strong
continuity of the continuum observable states.
-/
