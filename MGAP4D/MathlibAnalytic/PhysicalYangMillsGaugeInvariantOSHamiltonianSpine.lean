import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSYinYangSchrodingerBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianResolventLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSelfAdjoint
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIteratedDerivativeNorm
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
→ continuous linear real resolvent
→ sharp operator-norm bound by the inverse distance to the mass threshold
→ real resolvent identity
→ quantitative two-parameter resolvent continuity bound
→ bundled resolvent family on the open sub-mass interval
→ uniform delta⁻² Lipschitz control away from the mass threshold
→ local Lipschitz regularity and operator-norm continuity
→ operator-norm derivative R'_lambda = R_lambda²
→ continuous derivative and C¹ sub-mass resolvent regularity
→ C∞ sub-mass resolvent regularity
→ derivative of every resolvent composition power
→ exact all-order formula R_lambda^(n) = n! R_lambda^(n+1)
→ factorial Cauchy-type derivative norm bound
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
surjective.  Its inverse is bundled as a continuous linear endomorphism with
operator norm at most `(mass - lambda)⁻¹`.  For any two real parameters
`lambda, mu < mass`, the resolvents satisfy

```text
R_lambda - R_mu = (lambda - mu) R_lambda R_mu
```

and the quantitative estimate

```text
‖R_lambda - R_mu‖
  ≤ |lambda - mu| (mass - lambda)⁻¹ (mass - mu)⁻¹.
```

The resolvents are bundled as a single map from `Set.Iio mass` into the
operator-norm space of continuous linear endomorphisms.  On every truncated
sub-mass region `lambda ≤ mass - delta` with `delta > 0`, this family is
Lipschitz with constant `delta⁻²`, and is therefore locally Lipschitz and
continuous throughout the open interval.

The resolvent identity also gives the operator-norm difference quotient

```text
(lambda - mu)⁻¹ (R_lambda - R_mu) = R_lambda R_mu.
```

Passing to the limit with the established operator-norm continuity proves

```text
R'_lambda = R_lambda R_lambda.
```

Differentiating composition powers and inducting over the derivative order then
gives

```text
R_lambda^(n) = n! R_lambda^(n + 1).
```

Thus the real excitation resolvent is `C∞` on the full open sub-mass interval.
Combining the exact derivative formula with the sharp resolvent norm estimate
gives the Cauchy-type bound

```text
‖R_lambda^(n)‖ ≤ n! (mass - lambda)⁻(n + 1).
```

Point and continuous real spectrum below the transferred mass remain excluded
without assuming a native unbounded-operator spectrum object.

The remaining terminal inputs are a selected physical carrier and interpolation,
compatible gauge and reflection actions, positive-time observable restriction,
identification of the OS state with the continuum expectation state, and
observable-state strong continuity.  A real-time unitary group, vacuum
uniqueness, and a native complex spectral-calculus package for the unbounded
Hamiltonian are not constructed here.
-/
