import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfBoundaryIndependence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualProduct
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The strict-positive bulk Wilson amplitude written intrinsically on the
positive open-half coordinate.  The shared-boundary and negative-half slots are
fixed to identity because the strict-positive action does not see them. -/
noncomputable def periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      (fun _ => 1) x (fun _ => 1))

/-- The intrinsic positive open-half bulk amplitude is everywhere strictly
positive. -/
theorem periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude_pos
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H N beta x := by
  unfold periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  exact Real.exp_pos _

/-- Every boundary-fibered realization of the strict-positive bulk amplitude
is the same intrinsic function of the positive open-half coordinate. -/
theorem periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_openHalf
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H N beta x := by
  unfold periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude
  exact
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_boundary_y
      H N beta b (fun _ => 1) x y (fun _ => 1)

/-- The completed positive boundary amplitude separates exactly into a
strictly-positive open-half-only bulk factor and the complete literal product
of positive-boundary temporal relative Wilson kernels. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_openHalf_mul_fullTemporalKernelProduct
    {H N : ℕ}
    (hH : 0 < H)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b x =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H N beta x *
        (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeKernel N beta
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p)) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_eq_openHalf]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_boundaryFibered_eq_relativeKernelProduct
    hH beta b x (fun _ => 1)]

/-- The square-root boundary coefficient carried by the scalar Gram feature is
strictly positive.  This reuses the canonical boundary Gram positivity theorem
from the vacuum-moment layer rather than duplicating the declaration. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_sqrt_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 < Real.sqrt
      (periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b) := by
  exact Real.sqrt_pos.2
    (periodicHypercubicEvenBoundaryGramCoefficient_pos H N hN beta hbeta b)

/-- Exact three-factor form of the actual completed-positive scalar Gram
feature: open-half-only bulk amplitude, strictly-positive boundary square-root
coefficient, and the full literal positive-boundary temporal Wilson kernel
product.  This is the cancellation-free factorization needed for the final
injectivity step. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_openHalf_mul_boundarySqrt_mul_fullTemporalKernelProduct
    {H N : ℕ}
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H N beta x *
        (Real.sqrt
          (periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b) *
          (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
            specialUnitaryWilsonRelativeKernel N beta
              (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
              (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p))) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  rw [periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_openHalf_mul_fullTemporalKernelProduct
    hH beta b x]
  ring

end

end MathlibAnalytic
end MGAP4D
