import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalHalfSectorReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The boundary-conditioned negative completed Wilson amplitude is the positive
completed amplitude evaluated on the orientation-corrected open half. -/
theorem periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude_eq_positive_orientationCorrection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
        H N beta b y =
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b
        (periodicHypercubicEvenOpenHalfOrientationCorrection H y) := by
  unfold periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
      (fun _ => 1) y
  calc
    periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta A =
        periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
          (periodicHypercubicEvenConfigurationReflection H A) := by
      exact
        (periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_configurationReflection
          H N beta A).symm
    _ = periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          (periodicHypercubicEvenOpenHalfOrientationCorrection H y)
          (periodicHypercubicEvenOpenHalfOrientationCorrection H (fun _ => 1))) := by
      rw [show A =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          (fun _ => 1) y by rfl]
      rw [periodicHypercubicEvenConfigurationReflection_boundaryFiberedAssemble]
    _ = periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          (periodicHypercubicEvenOpenHalfOrientationCorrection H y)
          (fun _ => 1)) := by
      rw [periodicHypercubicEvenOpenHalfOrientationCorrection_one]

/-- Conversely, the boundary-conditioned positive completed Wilson amplitude is
the negative completed amplitude evaluated on the same orientation correction. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_negative_orientationCorrection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
        H N beta b x =
      periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude H N beta b
        (periodicHypercubicEvenOpenHalfOrientationCorrection H x) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenBoundaryCompletedNegativeWilsonAmplitude
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
      x (fun _ => 1)
  calc
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta A =
        periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
          (periodicHypercubicEvenConfigurationReflection H A) := by
      exact
        (periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_configurationReflection
          H N beta A).symm
    _ = periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          (periodicHypercubicEvenOpenHalfOrientationCorrection H (fun _ => 1))
          (periodicHypercubicEvenOpenHalfOrientationCorrection H x)) := by
      rw [show A =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          x (fun _ => 1) by rfl]
      rw [periodicHypercubicEvenConfigurationReflection_boundaryFiberedAssemble]
    _ = periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
          (fun _ => 1)
          (periodicHypercubicEvenOpenHalfOrientationCorrection H x)) := by
      rw [periodicHypercubicEvenOpenHalfOrientationCorrection_one]

end

end MathlibAnalytic
end MGAP4D
