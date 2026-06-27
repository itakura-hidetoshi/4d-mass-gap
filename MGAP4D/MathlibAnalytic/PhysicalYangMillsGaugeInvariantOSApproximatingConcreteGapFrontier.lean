import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumHalfQuadraticGap

/-!
# Concrete finite Wilson OS gap frontier

This aggregate exposes three theorem-generated routes.

```text
finite periodic SU(N) Wilson reflected-integral decay
→ half-time OS quadratic decay
→ observable-core and completed Hilbert decay
→ finite vacuum-sector gap certificate
```

```text
finite OS contractivity and reflection/time exchange
→ weak-star limits of quadratic and bilinear forms
→ continuum contraction semigroup
→ continuum transfer-operator symmetry
```

```text
continuum half-time OS quadratic decay
→ completed vacuum-sector semigroup decay
→ positive right-Hamiltonian Rayleigh lower bound
```

The remaining model-specific inputs are the common positive-time translation,
a uniform positive finite-volume decay slope, passage of that quantitative decay
to the continuum core, and strong continuity.
-/
