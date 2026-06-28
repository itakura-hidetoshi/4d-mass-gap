import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundedPointwiseBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryGapClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingMeasurableBoundaryL2FactorizedGap

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

boundary-moment AE strong measurability
+ squared-norm integrability
→ boundary L² membership

bounded measurable open-half Gram features
+ boundary transfer intertwining
+ exponential Poincaré defect inequality
    (1 - exp(-mass * t)) ‖v‖² ≤ ‖v‖² - ‖K_(n,t) v‖²
→ exact positive small-time slope mass
→ boundary L² quadratic transfer contraction
→ boundary transfer operator-norm contraction
→ integrated boundary-moment decay
→ continuum half-time OS quadratic gap with exact mass
→ self-adjoint graph-closed continuum OS Hamiltonian

measurable boundary moments
+ boundary feature analysis A_(n,t)
+ boundary feature synthesis S_(n,t)
+ K_(n,t) = S_(n,t) ∘ A_(n,t)
+ ‖S_(n,t)‖ ‖A_(n,t)‖ ≤ sqrt(q(t))
→ boundary transfer operator-norm contraction
→ the same finite and continuum gap route

boundary-moment decay
+ centered weak-star convergence
+ observable-state strong continuity
→ self-adjoint graph-closed continuum OS Hamiltonian
→ positive vacuum-orthogonal Rayleigh lower bound
→ unique zero-energy vacuum line
→ no nonzero eigenvector in the open mass gap
```

The pointwise, exponential boundary-`L²` Poincaré, and measurable
feature-factorized formulations are alternative finite-side interfaces.
The exponential route removes the abstract slope assumption and exposes a
direct finite-boundary-to-continuum-Hamiltonian constructor.
The remaining model-specific frontier is the scale-uniform strict Wilson
boundary estimate or an equivalent factorized operator-norm estimate.
-/
