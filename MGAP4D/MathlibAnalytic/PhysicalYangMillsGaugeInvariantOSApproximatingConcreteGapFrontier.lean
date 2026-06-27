import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSemigroup

/-!
# Concrete finite Wilson OS gap frontier

This aggregate exposes the theorem-generated route

```text
actual finite even-periodic SU(N) Wilson Gibbs reflected integrals
→ half-time OS quadratic decay
→ reflected OS bilinear decay
→ dense centered observable-core decay
→ completed finite OS Hilbert quadratic decay
→ finite transfer-operator norm decay
→ finite vacuum-orthogonal sector gap certificate
→ common-carrier continuum gap transfer
→ continuum closed-Hamiltonian Rayleigh lower bound
→ zero-energy space equals the normalized vacuum line
```

In parallel, finite-scale OS contractivity for one common positive-time
observable translation family passes automatically through weak-star convergence:

```text
finite Wilson OS quadratic contractions at every scale
→ pointwise convergence of OS quadratic values
→ continuum OS quadratic contraction
→ completed continuum physical contraction semigroup
```

The remaining model-specific frontier is now visible in finite-integral form:
construct the common positive-time translation action and prove a scale-uniform
strict decay inequality for the centered reflected Wilson Gibbs integrals with a
positive continuum slope.  Strong continuity and common-carrier convergence
must then be supplied for the final Hamiltonian transfer.
-/
