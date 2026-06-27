import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentGapClosure

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The exponential shared-boundary Poincaré estimate generates the integrated
boundary Gram-moment gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The exponential finite Wilson boundary estimate generates the continuum
half-time OS quadratic mass-gap certificate with exact mass `Q.mass`. -/
noncomputable def toContinuumHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.HalfQuadraticGapCertificate
      C.toContinuumPositiveTimeObservableContractionSemigroup :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toContinuumHalfQuadraticGapCertificate

/-- Exponential finite Wilson boundary decay and continuum observable-state
continuity produce a self-adjoint graph-closed continuum OS Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (hContinuous :
      C.toContinuumPositiveTimeObservableContractionSemigroup
        .StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        C.toContinuumPositiveTimeObservableContractionSemigroup
        hContinuous).closedRightHamiltonian := by
  exact Q.toApproximatingBoundaryMomentGapCertificate
    |>.closedRightHamiltonian_isSelfAdjoint hContinuous

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

end MathlibAnalytic
end MGAP4D

end
