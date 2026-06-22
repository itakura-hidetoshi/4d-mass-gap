import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensitySeparatedHalves
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedHalfAmplitudeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- After orientation correction of the negative open half, the transported
Wilson Gibbs density is an outer product of the same positive-half amplitude. -/
theorem periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_gramKernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal =
      (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta b y) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_boundary_mul_separatedHalves_div_partition]
  rw [periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude_eq_positive_orientationCorrection]
  rw [periodicHypercubicEvenOpenHalfOrientationCorrection_involutive H y]

end

end MathlibAnalytic
end MGAP4D
