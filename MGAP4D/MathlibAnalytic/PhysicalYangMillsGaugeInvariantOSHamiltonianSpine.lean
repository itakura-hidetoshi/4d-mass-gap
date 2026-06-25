import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSelfAdjoint
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventSurjective
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalTemporalAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSWeakLimitTimeReflection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumTimeReflection

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
→ exact finite-scale additive temporal action
→ dense lattice-time approximation by floor selectors
→ joint continuity for varying configurations and times
→ weak-limit continuum real-time invariance
→ continuum-only Euclidean-time action
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
→ complete vacuum-orthogonal excitation Hilbert sector
→ dense restricted Hamiltonian domain
→ excitation-sector positive-shift surjectivity
→ self-adjoint and graph-closed excitation Hamiltonian
→ transferred Rayleigh lower bound
→ coercive real-shift norm bound below the transferred mass
→ injective shifted excitation Hamiltonian
→ dense shifted range from self-adjointness
→ closed shifted range from graph closedness
→ real-shift surjectivity and bijectivity
→ linear real resolvent with quantitative inverse estimate
→ exclusion of the full real sub-mass spectrum
→ real Yin-Yang Schrödinger algebra bridge
```

The finite periodic lattice translations and their Wilson Gibbs invariance are
constructed.  Scale-dependent integer times, dense floor approximation, and
joint continuity now transport exact finite-time invariance to a genuine real
continuum action without assuming exact finite invariance at every target real
time.  The continuum-only reflection bridge feeds that action into the existing
OS symmetry and self-adjointness route.  The ambient resolvent then descends to
the vacuum-orthogonal carrier, where Mathlib supplies a self-adjoint and closed
excitation Hamiltonian.

For every real `lambda` below the transferred mass, the shifted excitation
Hamiltonian is injective, has dense and closed range, and is therefore
surjective.  It is bundled as a linear equivalence, and its inverse satisfies
the sharp coercive estimate determined by `mass - lambda`.  This excludes both
point and continuous real spectrum below the transferred mass without hiding a
native unbounded-operator spectrum object behind an additional assumption.

The remaining terminal inputs are a selected physical carrier and interpolation,
compatible gauge and reflection actions, positive-time observable restriction,
identification of the OS state with the continuum expectation state, and
observable-state strong continuity.  A real-time unitary group, vacuum
uniqueness, and a native complex spectral-calculus package for the unbounded
Hamiltonian are not constructed here.
-/
