import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensityFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialCrossingBoundaryDependence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The actual transported even-periodic Wilson Gibbs density separates into
positive and negative open-half amplitudes, a boundary-only spatial crossing
weight, the remaining time-containing crossing weight, and the partition
function normalization.

This is the exact density-level form needed before identifying the temporal
crossing factor with a boundary-conditioned Wilson RKHS Gram kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_temporal_crossing_div_partition
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta z).toReal =
      (periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2) *
        periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2) *
        (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
            H N beta z.1 *
          periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              z.1 z.2.1 z.2.2))) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_spatial_temporal_crossing_div_partition]
  rw [periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_boundaryFiberedAssemble_eq_boundary]

end

end MathlibAnalytic
end MGAP4D
