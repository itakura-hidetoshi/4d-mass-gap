import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonRangeMetricProjectionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A residual is orthogonal to the range of a real continuous linear
endomorphism when it is orthogonal to every image vector. -/
def IsContinuousLinearResidualOrthogonalToRange
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (f u : E) : Prop :=
  ∀ v : E, inner ℝ (f - A u) (A v) = 0

/-- The standard normal equation for a real continuous linear endomorphism. -/
def IsContinuousLinearNormalEquationSolution
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (f u : E) : Prop :=
  A (f - A u) = 0

/-- A projected normal equation, expressed through a proposed range projector. -/
def IsContinuousLinearProjectedNormalEquationSolution
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (C A : E →L[ℝ] E)
    (f u : E) : Prop :=
  C (f - A u) = 0

/-- Generic Hilbert-space direction: a residual orthogonal to the operator range
is a least-squares residual. -/
theorem isContinuousLinearLeastSquaresSolution_of_residualOrthogonalToRange
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (f u : E)
    (hOrthogonal : IsContinuousLinearResidualOrthogonalToRange A f u) :
    IsContinuousLinearLeastSquaresSolution A f u := by
  intro v
  have hDecomposition :
      f - A v = (f - A u) + A (u - v) := by
    rw [map_sub]
    abel
  have hInner :
      inner ℝ (f - A u) (A (u - v)) = 0 :=
    hOrthogonal (u - v)
  have hPythagoras :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (f - A u) (A (u - v)) hInner
  rw [hDecomposition]
  nlinarith [
    norm_nonneg (f - A u),
    norm_nonneg ((f - A u) + A (u - v)),
    norm_nonneg (A (u - v))]

/-- The cardinality-zero vacuum projector annihilates every ambient Poisson
image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_randomScanPoissonOperatorL2_eq_zero
    (u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
    zero_smul]

/-- Every least-squares residual is exactly the unavoidable vacuum component of
the datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_eq_vacuumProjector_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f := by
  have hPoisson :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f u).1 hLeastSquares
  calc
    f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
      f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
        rw [hPoisson]
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]
      abel

/-- Every least-squares residual is orthogonal to the full ambient Poisson
range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_residualOrthogonalToRange_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    IsContinuousLinearResidualOrthogonalToRange
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f u := by
  intro v
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_eq_vacuumProjector_of_isLeastSquaresSolution
      f u hLeastSquares,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    real_inner_smul_left,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
    mul_zero]

/-- Least-squares solutions are exactly the vectors whose residual is
orthogonal to every ambient Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_residualOrthogonalToRange
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      IsContinuousLinearResidualOrthogonalToRange
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_residualOrthogonalToRange_of_isLeastSquaresSolution
        f u
  · intro hOrthogonal
    exact
      isContinuousLinearLeastSquaresSolution_of_residualOrthogonalToRange
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u hOrthogonal

/-- A least-squares solution satisfies the standard Poisson normal equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_normalEquation_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    IsContinuousLinearNormalEquationSolution
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f u := by
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u) = 0
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_eq_vacuumProjector_of_isLeastSquaresSolution
      f u hLeastSquares,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_fluctuationCardinalityProjectorL2_zero_eq_zero]

/-- The standard Poisson normal equation forces the exact centered image and
therefore the least-squares property. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_of_randomScanPoisson_normalEquation
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hNormal :
      IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    IsContinuousLinearLeastSquaresSolution
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f u := by
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u) = 0 at hNormal
  have hKernelFix :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
      (f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u)).1 hNormal
  have hResidual :
      f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
    calc
      f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              u) := hKernelFix
      _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
                u) := by
        rw [map_sub]
      _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_randomScanPoissonOperatorL2_eq_zero,
          sub_zero]
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f u).2
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        u =
      f -
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u) := by
      abel
    _ =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
      rw [hResidual]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply
        f).symm

/-- The standard Poisson normal equation is equivalent to least squares. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_of_randomScanPoisson_normalEquation
        f u
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_normalEquation_of_isLeastSquaresSolution
        f u

/-- The projected normal equation through `C = I-E₀` is equivalent to the
standard Poisson normal equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isProjectedNormalEquationSolution_iff_isNormalEquationSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearProjectedNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u := by
  let r : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
    f -
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        u
  constructor
  · intro hProjected
    change periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 r = 0 at hProjected
    have hKernelFix :
        r =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 r := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]
        at hProjected
      exact sub_eq_zero.mp hProjected
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          r = 0
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
        r).2 hKernelFix
  · intro hNormal
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          r = 0 at hNormal
    have hKernelFix :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
        r).1 hNormal
    change periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 r = 0
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
      hKernelFix, sub_self]

/-- The projected normal equation is also equivalent to least squares. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isProjectedNormalEquationSolution_iff_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearProjectedNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isProjectedNormalEquationSolution_iff_isNormalEquationSolution,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution]

/-- The canonical generalized-inverse solution satisfies the standard normal
equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isNormalEquationSolution
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearNormalEquationSolution
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f) := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).2
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isLeastSquaresSolution
      f

/-- The canonical generalized-inverse solution satisfies residual orthogonality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_residualOrthogonalToRange
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearResidualOrthogonalToRange
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f) := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_residualOrthogonalToRange
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isLeastSquaresSolution
      f

/-- The normal-equation solution set is the affine vacuum family through the
canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_exists_eq_generalizedInverse_add_vacuumProjector
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      ∃ w : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 w := by
  constructor
  · intro hNormal
    have hLeastSquares :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
        f u).1 hNormal
    refine ⟨u, ?_⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_add_vacuumProjector_of_isLeastSquaresSolution
        f u hLeastSquares
  · rintro ⟨w, rfl⟩
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 w)).2
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_generalizedInverse_add_vacuumProjector_isLeastSquaresSolution
        f w

/-- The canonical generalized-inverse solution has minimum norm among all
normal-equation solutions. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_isNormalEquationSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hNormal :
      IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f‖ ≤ ‖u‖ := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_isLeastSquaresSolution
      f u
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
        f u).1 hNormal)

/-- A normal-equation solution with norm no larger than the canonical norm is
the canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_of_isNormalEquationSolution_of_norm_le
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hNormal :
      IsContinuousLinearNormalEquationSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u)
    (hNorm :
      ‖u‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_of_isLeastSquaresSolution_of_norm_le
      f u
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
        f u).1 hNormal)
      hNorm

/-- Structured receipt for the beta-zero Poisson normal-equation geometry. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonNormalEquationL2Receipt :
    Prop where
  least_squares_iff_residual_orthogonal :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u ↔
        IsContinuousLinearResidualOrthogonalToRange
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u
  normal_iff_least_squares :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearNormalEquationSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u ↔
        IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u
  projected_normal_iff_normal :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearProjectedNormalEquationSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u ↔
        IsContinuousLinearNormalEquationSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u
  affine_normal_solutions :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearNormalEquationSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u ↔
        ∃ w : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
          u =
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
                f +
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 w
  canonical_minimum_norm :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearNormalEquationSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u →
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f‖ ≤ ‖u‖

/-- Receipt constructor for the actual beta-zero Poisson normal-equation
geometry. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonNormalEquationL2Receipt :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonNormalEquationL2Receipt := by
  refine
    { least_squares_iff_residual_orthogonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_residualOrthogonalToRange
      normal_iff_least_squares :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_isLeastSquaresSolution
      projected_normal_iff_normal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isProjectedNormalEquationSolution_iff_isNormalEquationSolution
      affine_normal_solutions :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isNormalEquationSolution_iff_exists_eq_generalizedInverse_add_vacuumProjector
      canonical_minimum_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_isNormalEquationSolution }

end

end MathlibAnalytic
end MGAP4D
