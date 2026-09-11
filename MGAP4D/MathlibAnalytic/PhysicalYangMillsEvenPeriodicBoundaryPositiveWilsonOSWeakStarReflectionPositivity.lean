import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSWeakStarReflectionPositivity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Boundary-aware direct bridge from every positive-time physical observable
to the actual finite-volume even-periodic `SU(N)` Wilson Gibbs reflection form.

The finite observable may depend on the reflection-fixed time-zero boundary as
well as the positive open half.  This is the natural strengthened target for
local finite-range positive-time cylinder observables. -/
structure PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakStarBridge
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
      PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge
        S.toPhysicalFourDimensionalYangMillsWeakLimit
        halfExtent N hN beta hbeta
        (D.quadraticBoundedContinuousFunction F)

/-- Boundary-positive actual even-periodic Wilson Gibbs reflection positivity
implies reflection positivity of every embedded-lattice physical weak-star
state. -/
theorem physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_weakStarReflectionPositive
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  intro F
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction]
    using
      physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg
        S.toPhysicalFourDimensionalYangMillsWeakLimit
        halfExtent N hN beta hbeta
        (D.quadraticBoundedContinuousFunction F)
        (B.finiteBridge F) n

/-- Boundary-positive finite-volume Wilson Gibbs reflection positivity,
together with the direct physical pullback bridges, yields reflection
positivity of the continuum gauge-invariant weak-star state. -/
theorem physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_weakStarReflectionPositive
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  apply physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
    S D
  intro n
  exact
    physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_weakStarReflectionPositive
      S D halfExtent N hN beta hbeta B n

end

end MathlibAnalytic
end MGAP4D
