import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedVacuumOrthogonalBoundaryQuadraticGap

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- The half-time OS quadratic estimate generates the completed Hilbert-space
quadratic certificate through the existing reflected and observable-core
closures. -/
noncomputable def toApproximatingQuadraticGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toApproximatingReflectedQuadraticGapCertificate
    |>.toApproximatingObservableQuadraticGapCertificate
    |>.toApproximatingQuadraticGapCertificate

/-- Hence a half-time OS quadratic estimate already determines the actual
centered boundary-Haar `L²` quadratic-gap certificate. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toApproximatingQuadraticGapCertificate
    |>.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate

/-- And it determines the completed finite Wilson OS vacuum-gap certificate
through the actual centered boundary realization. -/
noncomputable def toCompletedVacuumOrthogonalApproximatingVacuumGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- The single finite periodic Wilson Gibbs reflected-integral estimate now
feeds all the way through the actual centered boundary-Haar `L²` realization.

After the field `finite_integral_decay`, every step here is theorem-generated:
finite reflected integral = OS quadratic value, half-time/reflected/observable
closures, Hilbert completion, physical boundary isometry, vacuum-orthogonal
projection, and the global boundary quadratic contraction. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toApproximatingHalfQuadraticGapCertificate
    |>.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate

/-- Direct operator-norm boundary-transfer certificate from the finite
reflected-integral estimate. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryL2TransferGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryL2TransferGapCertificate

/-- Direct integrated actual boundary-moment certificate from the finite
reflected-integral estimate. -/
noncomputable def toCompletedVacuumOrthogonalBoundaryMomentGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The finite reflected-integral estimate therefore generates the completed
finite Wilson OS vacuum-gap certificate via the actual boundary realization,
with no actual-adjoint/open-half factorization hypothesis. -/
noncomputable def toCompletedVacuumOrthogonalApproximatingVacuumGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C :=
  R.toCompletedVacuumOrthogonalBoundaryL2QuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

end MathlibAnalytic
end MGAP4D

end
