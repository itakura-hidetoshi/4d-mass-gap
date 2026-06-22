import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorBoundaryFiberedDependence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Boundary-conditioned completed positive Wilson amplitude.  The unused
negative-half coordinate is fixed to the identity configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1))

/-- Boundary-conditioned completed negative Wilson amplitude.  The unused
positive-half coordinate is fixed to the identity configuration. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b (fun _ => 1) y)

/-- Every realization of the completed positive amplitude equals its explicit
boundary-and-positive-half representative. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_boundaryCompletedPositive
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y) =
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
        H N beta b x := by
  exact
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_y
      H N beta b x y (fun _ => 1)

/-- Every realization of the completed negative amplitude equals its explicit
boundary-and-negative-half representative. -/
theorem periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_boundaryCompletedNegative
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y) =
      periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
        H N beta b y := by
  exact
    periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_x
      H N beta b x (fun _ => 1) y

/-- Exact separated-half factorization of the actual transported finite-volume
Wilson Gibbs density.  The positive amplitude reads only `(b,x)`, the negative
amplitude reads only `(b,y)`, and the remaining crossing weight is boundary
only. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_boundary_mul_separatedHalves_div_partition
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
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
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta z.1 z.2.1 *
        periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
          H N beta z.1 z.2.2) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_boundary_mul_completedPositive_mul_completedNegative_div_partition]
  rw [periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_boundaryCompletedPositive]
  rw [periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_boundaryCompletedNegative]

end

end MathlibAnalytic
end MGAP4D
