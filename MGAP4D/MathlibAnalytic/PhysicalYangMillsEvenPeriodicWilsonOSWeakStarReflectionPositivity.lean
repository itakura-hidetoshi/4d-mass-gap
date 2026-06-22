import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSWeakLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantWeakStarReflectionPositivity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The bounded continuous physical representative of the real
Osterwalder--Schrader quadratic observable `Theta(F) * F`. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) :
    BoundedContinuousFunction S.Configuration ℝ :=
  ((D.quadraticObservable F :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    BoundedContinuousFunction S.Configuration ℝ)

/-- Concrete bridge from every positive-time physical observable to the actual
finite-volume even-periodic `SU(N)` Wilson Gibbs reflection form.

Unlike `PhysicalYangMillsFiniteWilsonOSWeakStarBridge`, this bridge does not
route through an abstract finite approximation family.  Each physical
quadratic observable is pulled back directly to the bounded continuous
positive-half observable used by the actual Wilson Gibbs reflection-positivity
theorem. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n) where
  finiteBridge :
    ∀ F : D.positiveTimeSubalgebra,
      PhysicalYangMillsEvenPeriodicWilsonOSWeakLimitBridge
        S.toPhysicalFourDimensionalYangMillsWeakLimit
        halfExtent N hN beta hbeta
        (D.quadraticBoundedContinuousFunction F)

/-- Actual even-periodic Wilson Gibbs reflection positivity implies
reflection positivity of every embedded-lattice physical weak-star state. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_weakStarReflectionPositive
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  intro F
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction]
    using
      physical_yang_mills_evenPeriodicWilsonOS_approximating_nonneg
        S.toPhysicalFourDimensionalYangMillsWeakLimit
        halfExtent N hN beta hbeta
        (D.quadraticBoundedContinuousFunction F)
        (B.finiteBridge F) n

/-- Actual finite-volume even-periodic Wilson Gibbs reflection positivity,
together with the direct physical pullback bridges, yields reflection
positivity of the continuum gauge-invariant weak-star state. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_weakStarReflectionPositive
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  apply physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
    S D
  intro n
  exact
    physical_yang_mills_evenPeriodicWilsonOS_approximating_weakStarReflectionPositive
      S D halfExtent N hN beta hbeta B n

end

end MathlibAnalytic
end MGAP4D
