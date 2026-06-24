import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

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
→ configuration-space time-translation homeomorphisms
→ induced gauge-invariant observable automorphisms
→ continuum-measure invariance and continuum-state identification
→ reflection/time-translation covariance
→ observable OS exchange identity
→ completed semigroup inner-product symmetry
→ right generator and Hamiltonian formal symmetry
→ graph-closed Hamiltonian formal symmetry
→ conditional closed Hamiltonian self-adjointness
→ real Yin-Yang Schrödinger algebra bridge
```

The terminal self-adjointness theorem remains conditional on configuration-space
time-translation homeomorphisms commuting with gauge transformations, preserving
the continuum law, restricting to the positive-time contraction semigroup, and
obeying reflection covariance.  The OS state must be identified with the actual
continuum expectation state.  This module does not construct the physical
configuration translations themselves, a real-time unitary group, vacuum
uniqueness, or a positive spectral gap.
-/
