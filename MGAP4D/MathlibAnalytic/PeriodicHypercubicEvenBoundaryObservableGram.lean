import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodicHypercubicEvenBoundaryObservableGramFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b x * f x

theorem periodicHypercubicEvenBoundaryDensity_mul_observable_eq_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y) =
      inner ℝ
        (periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f b x)
        (periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f b y) := by
  rw [periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner]
  simp [periodicHypercubicEvenBoundaryObservableGramFeature]
  ring

end

end MathlibAnalytic
end MGAP4D
