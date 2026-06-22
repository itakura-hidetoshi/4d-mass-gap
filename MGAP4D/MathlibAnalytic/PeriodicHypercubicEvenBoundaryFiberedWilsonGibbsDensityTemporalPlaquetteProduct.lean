import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensityBoundaryTemporal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingWilsonBoltzmannProduct

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The actual transported Wilson Gibbs density is the product of the two
open-half amplitudes, a boundary-only spatial crossing weight, and the finite
product of temporal crossing Wilson central functions, divided by the partition
function.

This is the final purely algebraic density decomposition before each temporal
plaquette factor is identified with a boundary-conditioned RKHS inner product. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_temporalPlaquette_product_div_partition
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
          (∏ p : PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H,
            specialUnitaryWilsonBoltzmannCentralFunction N beta
              (periodicHypercubicPlaquetteHolonomy
                ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                  z.1 z.2.1 z.2.2)
                p.1)))) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_boundary_temporal_crossing_div_partition]
  rw [periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_plaquette_product]

end

end MathlibAnalytic
end MGAP4D
