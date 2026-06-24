import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalTemporalAction
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
→ periodic vertex, edge, plaquette, and configuration translations
→ concrete integer temporal translations along coordinate zero
→ plaquette-holonomy and Wilson-action translation invariance
→ product-Haar and finite Gibbs translation invariance
→ canonical physical temporal-action constructor
→ interpolation equivariance
→ embedded approximating-law invariance
→ weak-limit continuum-time invariance
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

The finite periodic lattice translations and their Wilson Gibbs invariance are now
constructed.  The canonical physical temporal-action constructor automatically
supplies finite-law invariance from scale-dependent periodic displacements.
The terminal self-adjointness theorem remains conditional on a physical real-time
Euclidean translation action, interpolation equivariance with the selected lattice
displacements, compatible gauge and reflection actions, positive-time restriction,
and identification of the OS state with the continuum expectation state.  A
real-time unitary group, vacuum uniqueness, and a positive spectral gap are not
constructed here.
-/
