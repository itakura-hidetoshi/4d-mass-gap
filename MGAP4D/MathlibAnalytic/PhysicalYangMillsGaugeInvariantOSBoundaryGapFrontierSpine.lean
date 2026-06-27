import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundedPointwiseBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentGapClosure

/-!
# Concrete Wilson OS boundary-gap frontier spine

This aggregate exposes three compatible local interfaces for the remaining
finite-volume mass-gap estimate.

```text
bounded measurable open-half Gram features
+ pointwise shared-boundary moment decay
→ integrated boundary-moment decay
→ full finite reflected-integral decay
→ finite Wilson OS vacuum-sector norm decay

boundary L² transfer-operator contraction
→ integrated boundary-moment decay
→ the same finite and continuum gap route

boundary-moment decay
+ centered weak-star convergence
+ observable-state strong continuity
→ self-adjoint graph-closed continuum OS Hamiltonian
→ positive vacuum-orthogonal Rayleigh lower bound
→ unique zero-energy vacuum line
→ no nonzero eigenvector in the open mass gap
```

The pointwise and boundary-`L²` formulations are alternative finite-side
interfaces.  Neither supplies the scale-uniform strict contraction itself.
That quantitative Wilson estimate, together with a positive continuum slope,
remains the model-specific mathematical frontier.
-/
