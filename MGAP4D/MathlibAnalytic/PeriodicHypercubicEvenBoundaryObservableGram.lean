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
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  simp only [periodicHypercubicEven_real_inner_eq_mul]
  ring

/-- On the reflected diagonal, the boundary-conditioned Wilson Gibbs observable
kernel is exactly the square of its scalar Gram feature. -/
theorem periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_eq_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal *
        (f x * f x) =
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x) ^ 2 := by
  rw [periodicHypercubicEvenBoundaryDensity_mul_observable_eq_inner]
  rw [periodicHypercubicEven_real_inner_eq_mul]
  rw [pow_two]

/-- Pointwise nonnegativity of the reflected diagonal observable kernel.  This is
its finite-volume boundary-fiber Gram positivity before integration. -/
theorem periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal *
        (f x * f x) := by
  rw [periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_eq_sq]
  exact sq_nonneg _

end

end MathlibAnalytic
end MGAP4D
