import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonMoorePenroseL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A vector is a least-squares solution for a continuous linear endomorphism
when its residual norm is no larger than the residual norm of any competitor. -/
def IsContinuousLinearLeastSquaresSolution
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (f u : E) : Prop :=
  ∀ v : E, ‖f - A u‖ ≤ ‖f - A v‖

/-- The residual of the canonical generalized-inverse solution is exactly the
cardinality-zero Gibbs-vacuum component of the datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_generalizedInverse_eq_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector]
  abel

/-- Every residual splits into its unavoidable vacuum component and a centered
mismatch lying in the Poisson range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_residual_eq_vacuumProjector_add_centeredMismatch
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f +
        ((f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u) := by
  abel

/-- The unavoidable vacuum residual is orthogonal to every centered mismatch. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuumProjector_centeredMismatch_eq_zero
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)
        ((f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u) = 0 := by
  have hCenteredExpanded :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (f -
            inner ℝ
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
                f •
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2) = 0 := by
    simpa only [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
        f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    real_inner_smul_left, inner_sub_right, hCenteredExpanded,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
    sub_self, mul_zero]

/-- The canonical least-squares residual is orthogonal to the entire Poisson
range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_leastSquaresResidual_generalizedInverse_poissonImage_eq_zero
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_generalizedInverse_eq_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    real_inner_smul_left,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
    mul_zero]

/-- Exact Pythagorean identity for the residual of every competitor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_randomScanPoisson_residual_eq_norm_sq_vacuumProjector_add_norm_sq_centeredMismatch
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u‖ *
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ =
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖ *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖ +
      ‖(f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u‖ *
        ‖(f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_residual_eq_vacuumProjector_add_centeredMismatch]
  exact
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f)
      ((f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuumProjector_centeredMismatch_eq_zero
        f u)

/-- The vacuum component is the exact lower bound for every residual norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_vacuumProjector_le_norm_randomScanPoisson_residual
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f‖ ≤
      ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u‖ := by
  have hPythagoras :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_randomScanPoisson_residual_eq_norm_sq_vacuumProjector_add_norm_sq_centeredMismatch
      f u
  nlinarith [
    norm_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f),
    norm_nonneg
      (f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u),
    norm_nonneg
      ((f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u)]

/-- The canonical generalized-inverse solution minimizes the residual norm for
arbitrary ambient data, without assuming exact Poisson solvability. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_leastSquaresResidual_generalizedInverse_le
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)‖ ≤
      ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_generalizedInverse_eq_vacuumProjector]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_vacuumProjector_le_norm_randomScanPoisson_residual
      f u

/-- Equality in the least-squares residual bound occurs exactly when the
competitor has the same centered Poisson image as the canonical solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_residual_eq_minimum_iff_poisson_eq_centering
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u‖ =
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)‖ ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_generalizedInverse_eq_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_residual_eq_vacuumProjector_add_centeredMismatch]
  have hInner :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuumProjector_centeredMismatch_eq_zero
      f u
  constructor
  · intro hNorm
    have hZero :=
      (norm_add_eq_norm_left_iff_of_inner_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)
        ((f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u)
        hInner).1 hNorm
    have hEq :
        f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u :=
      sub_eq_zero.mp hZero
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f := hEq.symm
      _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply
          f).symm
  · intro hPoisson
    apply
      (norm_add_eq_norm_left_iff_of_inner_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)
        ((f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u)
        hInner).2
    apply sub_eq_zero.mpr
    calc
      f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f :=
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply
            f).symm
      _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u := hPoisson.symm

/-- The generalized inverse is a least-squares solution for every ambient
datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isLeastSquaresSolution
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearLeastSquaresSolution
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f) := by
  intro u
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_leastSquaresResidual_generalizedInverse_le
      f u

/-- A vector is a least-squares solution exactly when its Poisson image is the
orthogonal centering of the datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  constructor
  · intro hLeastSquares
    have hUpper :=
      hLeastSquares
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_leastSquaresResidual_generalizedInverse_le
        f u
    have hEquality := le_antisymm hUpper hLower
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_residual_eq_minimum_iff_poisson_eq_centering
        f u).1 hEquality
  · intro hPoisson v
    have hEquality :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_residual_eq_minimum_iff_poisson_eq_centering
        f u).2 hPoisson
    calc
      ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ =
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)‖ := hEquality
      _ ≤
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            v‖ :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_leastSquaresResidual_generalizedInverse_le
            f v

/-- The generalized inverse ignores the unavoidable vacuum component of the
datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_centeringEnd_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  have hCenter :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)) :=
        congrArg
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          hCenter
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
        f

/-- Every least-squares solution is the canonical generalized-inverse solution
plus its exact vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_add_vacuumProjector_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u := by
  have hPoisson :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f u).1 hLeastSquares
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      u hPoisson
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_centeringEnd_eq_self]
    at hDecomposition
  exact hDecomposition

/-- Every affine vacuum translate of the canonical solution is a least-squares
solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_generalizedInverse_add_vacuumProjector_isLeastSquaresSolution
    (f w : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsContinuousLinearLeastSquaresSolution
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 w) := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 w)).2
  rw [map_add,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_fluctuationCardinalityProjectorL2_zero_eq_zero,
    add_zero,
    ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- The canonical generalized-inverse solution has minimum norm among all
least-squares solutions. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f‖ ≤ ‖u‖ := by
  have hPoisson :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f u).1 hLeastSquares
  have hMinimum :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      u hPoisson
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_centeringEnd_eq_self]
    at hMinimum
  exact hMinimum

/-- A least-squares solution whose norm is no larger than the canonical norm is
exactly the canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_of_isLeastSquaresSolution_of_norm_le
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u)
    (hNorm :
      ‖u‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  have hPoisson :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      f u).1 hLeastSquares
  have hNormCentered :
      ‖u‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)‖ := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_centeringEnd_eq_self]
    exact hNorm
  calc
    u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_of_randomScanPoissonOperatorL2_apply_eq_of_norm_le
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
        u hPoisson hNormCentered
    _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_centeringEnd_eq_self
        f

/-- Among least-squares solutions, equality with the canonical norm is
equivalent to equality with the canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_eq_generalizedInverse_of_isLeastSquaresSolution
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hLeastSquares :
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f u) :
    ‖u‖ =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f := by
  constructor
  · intro hNorm
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_of_isLeastSquaresSolution_of_norm_le
        f u hLeastSquares hNorm.le
  · intro hu
    rw [hu]

/-- Structured receipt for the arbitrary-data beta-zero least-squares geometry. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonLeastSquaresL2Receipt :
    Prop where
  canonical_residual :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f
  pythagorean_residual :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ *
          ‖f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              u‖ =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f‖ *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f‖ +
        ‖(f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ *
          ‖(f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              u‖
  canonical_least_squares :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
  least_squares_iff :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u ↔
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f
  affine_classification :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u →
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 u
  minimum_norm :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u →
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f‖ ≤ ‖u‖
  unique_minimum_norm :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsContinuousLinearLeastSquaresSolution
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f u →
        ‖u‖ ≤
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f‖ →
          u =
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f

/-- The arbitrary-data beta-zero least-squares receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonLeastSquaresL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonLeastSquaresL2Receipt := by
  refine
    { canonical_residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_leastSquaresResidual_generalizedInverse_eq_vacuumProjector
      pythagorean_residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_randomScanPoisson_residual_eq_norm_sq_vacuumProjector_add_norm_sq_centeredMismatch
      canonical_least_squares :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isLeastSquaresSolution
      least_squares_iff :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_isLeastSquaresSolution_iff_poisson_eq_centering
      affine_classification :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_add_vacuumProjector_of_isLeastSquaresSolution
      minimum_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_isLeastSquaresSolution
      unique_minimum_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_generalizedInverse_of_isLeastSquaresSolution_of_norm_le }

end

end MathlibAnalytic
end MGAP4D
