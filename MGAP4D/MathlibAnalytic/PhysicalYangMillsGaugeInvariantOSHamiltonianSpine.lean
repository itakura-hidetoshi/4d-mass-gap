import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedTemporalSymmetryLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSWeakLimitTimeReflection

/-!
# Physical gauge-invariant OS Hamiltonian spine

This aggregate module exposes the completed analytic route

```text
positive-time observable algebra
→ physical contraction semigroup
→ strong continuity
→ right infinitesimal generator
→ right Hamiltonian
→ semigroup covariance
→ Bochner time averages
→ dense generator domain
→ nonnegative Hamiltonian form
→ finite-time Laplace resolvent identity
→ positive-shift surjectivity and bijectivity
→ maximal-accretive package
→ formal symmetry implies self-adjointness
→ finite-lattice Euclidean-time transformations
→ finite Gibbs invariance and interpolation equivariance
→ embedded approximating-law invariance
→ weak-limit continuum-time invariance
→ configuration-space time-translation homeomorphisms
→ configuration-space reflection homeomorphism
→ gauge covariance and reflection/time exchange on configurations
→ induced gauge-invariant observable automorphisms
→ continuum-state identification
→ observable reflection/time-translation covariance
→ observable OS exchange identity
→ completed semigroup inner-product symmetry
→ right generator and Hamiltonian formal symmetry
→ graph-closed Hamiltonian formal symmetry
→ conditional closed Hamiltonian self-adjointness
→ real Yin-Yang Schrödinger algebra bridge
```

The terminal self-adjointness theorem remains conditional on concrete finite-lattice
time transformations preserving the Wilson Gibbs laws and compatible with physical
interpolation, together with a compatible continuum reflection, positive-time
restriction, and identification of the OS state with the continuum expectation
state.  Continuum time-translation invariance is derived from the embedded laws
and weak convergence.  This module does not yet construct the periodic lattice
time transformations themselves, a real-time unitary group, vacuum uniqueness,
or a positive spectral gap.
-/
