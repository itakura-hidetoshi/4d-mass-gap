import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSObservableTimeTranslationCovariance

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
→ full observable time-translation automorphisms
→ reflection/time-translation covariance and state invariance
→ observable OS exchange identity
→ completed semigroup inner-product symmetry
→ right generator and Hamiltonian formal symmetry
→ graph-closed Hamiltonian formal symmetry
→ conditional closed Hamiltonian self-adjointness
→ real Yin-Yang Schrödinger algebra bridge
```

The terminal self-adjointness theorem remains conditional on full-observable
time-translation automorphisms whose positive-time restriction is the supplied
contraction semigroup, together with reflection covariance, state invariance,
and observable-state strong continuity.  This module does not construct those
full translations, a real-time unitary group, vacuum uniqueness, or a positive
spectral gap.
-/
