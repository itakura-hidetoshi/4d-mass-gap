import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensityBoundaryTemporal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The actual boundary-fibered Wilson Gibbs density separates into the two
open-half bulk amplitudes, the boundary-only spatial crossing weight, the
positive-boundary temporal weight, the negative-boundary temporal weight, and
the partition-function normalization. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_positiveTemporal_negativeTemporal_div_partition
    (H N : ℕ) (hN : 0 < N)
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
          (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
              H N beta
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                z.1 z.2.1 z.2.2) *
            periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
              H N beta
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                z.1 z.2.1 z.2.2)))) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_temporal_crossing_div_partition]
  rw [periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_positiveBoundary_mul_negativeBoundary]

/-- The positive bulk amplitude completed by the temporal plaquettes adjacent to
the fixed planes from the positive side. -/
noncomputable def periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta A *
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
      H N beta A

/-- The negative bulk amplitude completed by the temporal plaquettes adjacent
to the fixed planes from the negative side. -/
noncomputable def periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta A *
    periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
      H N beta A

/-- Equivalent completed-half factorization of the actual transported Wilson
Gibbs density.  The only remaining crossing factor is the boundary-only spatial
weight. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_boundary_mul_completedPositive_mul_completedNegative_div_partition
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
      (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta z.1 *
        periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
          H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2) *
        periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
          H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2)) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_positiveTemporal_negativeTemporal_div_partition]
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
  ring

end

end MathlibAnalytic
end MGAP4D
