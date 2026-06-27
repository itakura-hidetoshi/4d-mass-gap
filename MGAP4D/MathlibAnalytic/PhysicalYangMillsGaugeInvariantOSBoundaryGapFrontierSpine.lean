import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundedPointwiseBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundedBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentGapClosure

/-!
# Concrete Wilson OS boundary-gap frontier spine

This aggregate exposes the compatible local interfaces for the remaining
finite-volume mass-gap estimate.

```text
bounded measurable open-half Gram features
+ pointwise shared-boundary moment decay
→ integrated boundary-moment decay
→ full finite reflected-integral decay
→ finite Wilson OS vacuum-sector norm decay

boundary L² Poincaré defect inequality
→ boundary L² quadratic transfer contraction
→ boundary transfer operator-norm contraction
→ integrated boundary-moment decay
→ the same finite and continuum gap route

bounded measurable open-half Gram features
+ boundary L² membership
+ boundary transfer intertwining
+ boundary transfer contraction
→ integrated boundary-moment decay

boundary-moment decay
+ centered weak-star convergence
+ observable-state strong continuity
→ self-adjoint graph-closed continuum OS Hamiltonian
→ positive vacuum-orthogonal Rayleigh lower bound
→ unique zero-energy vacuum line
→ no nonzero eigenvector in the open mass gap
```

The pointwise, boundary-`L²` quadratic, and boundary-`L²` Poincaré formulations
are alternative finite-side interfaces.  None supplies the scale-uniform strict
defect itself.  That quantitative Wilson estimate, together with a positive
continuum slope, remains the model-specific mathematical frontier.
-/
