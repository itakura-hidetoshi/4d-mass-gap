import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanCenteredGreenCovarianceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A symmetric strictly positive continuous linear endomorphism induces the
Cauchy--Schwarz inequality for its quadratic form. -/
theorem continuousLinearMap_inner_apply_sq_le_self_mul_self_of_symm_pos
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y))
    (hPos : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (x y : E) :
    inner ℝ (T x) y ^ 2 ≤
      inner ℝ (T x) x * inner ℝ (T y) y := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hyy : 0 < inner ℝ (T y) y := hPos y hy
    have hCross : inner ℝ (T y) x = inner ℝ (T x) y := by
      calc
        inner ℝ (T y) x = inner ℝ y (T x) := hSymm y x
        _ = inner ℝ (T x) y := real_inner_comm _ _
    let t : ℝ := inner ℝ (T x) y / inner ℝ (T y) y
    have hNonneg :
        0 ≤ inner ℝ (T (x - t • y)) (x - t • y) := by
      by_cases hZero : x - t • y = 0
      · rw [hZero]
        simp
      · exact le_of_lt (hPos (x - t • y) hZero)
    have hExpand :
        inner ℝ (T (x - t • y)) (x - t • y) =
          inner ℝ (T x) x -
            2 * t * inner ℝ (T x) y +
            t ^ 2 * inner ℝ (T y) y := by
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hCross]
      ring
    rw [hExpand] at hNonneg
    have hMul := mul_nonneg (le_of_lt hyy) hNonneg
    have hIdentity :
        inner ℝ (T y) y *
            (inner ℝ (T x) x -
              2 * t * inner ℝ (T x) y +
              t ^ 2 * inner ℝ (T y) y) =
          inner ℝ (T x) x * inner ℝ (T y) y -
            inner ℝ (T x) y ^ 2 := by
      dsimp [t]
      field_simp [ne_of_gt hyy]
      <;> ring
    rw [hIdentity] at hMul
    nlinarith

/-- The actual beta-zero centered Green covariance satisfies its intrinsic
Cauchy--Schwarz inequality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_sq_le_self_mul_self
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          g g := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  apply
    continuousLinearMap_inner_apply_sq_le_self_mul_self_of_symm_pos
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
  · intro x hx
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_le_randomScanCenteredGreenCovarianceL2_self
        x
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2 at hLower
    have hNormPos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hNormSqPos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hNormPos
    exact lt_of_lt_of_le hNormSqPos hLower

/-- Absolute-value form of the intrinsic Green covariance Cauchy--Schwarz
inequality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_sqrt_self_mul_sqrt_self
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f g| ≤
      Real.sqrt
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f f) *
        Real.sqrt
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            g g) := by
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_sq_le_self_mul_self
      f g
  have hFNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_nonneg
      f
  have hGNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_nonneg
      g
  have hRightNonneg :
      0 ≤
        Real.sqrt
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
              f f) *
          Real.sqrt
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
              g g) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSq' :
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g| ^ 2 ≤
        (Real.sqrt
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
                f f) *
            Real.sqrt
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
                g g)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hFNonneg, Real.sq_sqrt hGNonneg]
    exact hSq
  nlinarith [abs_nonneg
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
      f g)]

/-- Quadratic expansion of the centered Green covariance on a sum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_add_self
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        (f + g) (f + g) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f +
        2 *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f g +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          g g := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  have hCross :
      inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
    calc
      inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        inner ℝ
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
        exact
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
            g f
      _ = inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
        real_inner_comm _ _
  change
    inner ℝ
        (((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        ((f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) =
      inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
        2 *
          inner ℝ
            ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
              Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (g : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
        inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [inner_add_left, inner_add_right, inner_add_right, hCross]
  ring

/-- Quadratic scaling of the centered Green covariance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_smul_self
    (a : ℝ)
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        (a • f) (a • f) =
      a ^ 2 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  change
    inner ℝ
        (a •
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (a •
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) =
      a ^ 2 *
        inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The intrinsic centered Green energy magnitude. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  Real.sqrt
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
      f f)

/-- The square of the Green energy magnitude is the covariance diagonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ^ 2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f f := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
  rw [Real.sq_sqrt]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_nonneg
      f

/-- The Green energy magnitude is nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f := by
  exact Real.sqrt_nonneg _

/-- The Green energy magnitude vanishes exactly at zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f = 0 ↔
      f = 0 := by
  constructor
  · intro hZero
    have hSq :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
        f
    rw [hZero] at hSq
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_eq_zero_iff
        f).1
    nlinarith
  · intro hZero
    rw [hZero]
    simp [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2]

/-- Absolute homogeneity of the Green energy magnitude. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul
    (a : ℝ)
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (a • f) =
      |a| *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f := by
  have hLeftSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      (a • f)
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_smul_self]
    at hLeftSq
  have hRightSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      f
  have hEqSq :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (a • f) ^ 2 =
        (|a| *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f) ^ 2 := by
    rw [hLeftSq, mul_pow, sq_abs, hRightSq]
  have hLeftNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      (a • f)
  have hRightNonneg :
      0 ≤
        |a| *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f :=
    mul_nonneg (abs_nonneg a)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
  nlinarith

/-- Triangle inequality for the Green energy magnitude. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_add_le
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (f + g) ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          g := by
  have hSumSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      (f + g)
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_add_self]
    at hSumSq
  have hFSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      f
  have hGSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      g
  have hCS :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_sqrt_self_mul_sqrt_self
      f g
  change
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f g| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          g at hCS
  have hCross :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            g :=
    le_trans (le_abs_self _) hCS
  have hSumNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      (f + g)
  have hFNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      f
  have hGNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      g
  nlinarith

/-- Intrinsic covariance Cauchy--Schwarz expressed in Green energy magnitudes. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_greenEnergyNorm_mul_greenEnergyNorm
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f g| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          g := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_sqrt_self_mul_sqrt_self
      f g

/-- Exact ambient/Green-energy norm equivalence. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_bounds
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖f‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ≤
        18 * ‖f‖ := by
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      f
  have hBounds :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_bounds
      f
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      f
  have hNormNonneg := norm_nonneg f
  constructor
  · nlinarith
  · nlinarith

/-- The lower Green-energy equivalence constant one is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenEnergyNormL2_eq_norm
    : ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        f ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f = ‖f‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_norm_sq
    with ⟨f, hfNe, hDiagonal⟩
  refine ⟨f, hfNe, ?_⟩
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      f
  rw [hDiagonal] at hSq
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      f
  nlinarith [norm_nonneg f]

/-- The upper Green-energy equivalence constant eighteen is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenEnergyNormL2_eq_18_mul_norm
    : ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        f ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f = 18 * ‖f‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq
    with ⟨f, hfNe, hDiagonal⟩
  refine ⟨f, hfNe, ?_⟩
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
      f
  rw [hDiagonal] at hSq
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      f
  nlinarith [norm_nonneg f]

/-- Sharp lower quadratic-form bound for the internal beta-zero Poisson map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 324) * ‖u‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u)
        u := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      u.property
  change
    ((1 : ℝ) / 324) *
        ‖(u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hOrthogonal

/-- Sharp upper quadratic-form bound for the internal beta-zero Poisson map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_le_norm_sq
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u)
        u ≤
      ‖u‖ ^ 2 := by
  change
    inner ℝ
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ≤
      ‖(u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm_le_norm_sq
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The intrinsic Poisson/Dirichlet energy magnitude. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  Real.sqrt
    (inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        u)
      u)

/-- The square of the Poisson energy magnitude is the Dirichlet quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ^ 2 =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u)
        u := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
  rw [Real.sq_sqrt]
  exact le_trans
    (mul_nonneg (by norm_num) (sq_nonneg ‖u‖))
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
      u)

/-- Poisson energy is Green energy of the Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u) := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self]
  rw [real_inner_comm]

/-- The Poisson energy magnitude is nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u := by
  exact Real.sqrt_nonneg _

/-- The Poisson energy magnitude vanishes exactly at zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u = 0 ↔
      u = 0 := by
  constructor
  · intro hZero
    have hSq :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
        u
    rw [hZero] at hSq
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
        u
    rw [← hSq] at hLower
    have hNormZero : ‖u‖ = 0 := by
      nlinarith [norm_nonneg u]
    exact norm_eq_zero.mp hNormZero
  · intro hZero
    rw [hZero]
    simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2]

/-- Absolute homogeneity of the Poisson energy magnitude. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul
    (a : ℝ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        (a • u) =
      |a| *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson,
    map_smul,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul,
    ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson]

/-- Triangle inequality for the Poisson energy magnitude. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_add_le
    (u v : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        (u + v) ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          v := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson,
    map_add]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            v) ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u) +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            v) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_add_le
        _ _
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          v := by
      rw [
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson,
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson]

/-- Exact ambient/Poisson-energy norm equivalence. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 18) * ‖u‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ≤
        ‖u‖ := by
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u
  have hLower :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
      u
  have hUpper :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_le_norm_sq
      u
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      u
  have hNormNonneg := norm_nonneg u
  constructor
  · nlinarith
  · nlinarith

/-- The lower Poisson-energy equivalence constant `1 / 18` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonEnergyNormL2_eq_inv_18_mul_norm
    : ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        u ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u =
          ((1 : ℝ) / 18) * ‖u‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨u, huNe, hAction⟩
  refine ⟨u, huNe, ?_⟩
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u
  rw [hAction] at hSq
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ^ 2 =
      inner ℝ
        (((1 : ℝ) / 324) •
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) at hSq
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hSq
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      u
  nlinarith [hSq, norm_nonneg u]

/-- The upper Poisson-energy equivalence constant one is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonEnergyNormL2_eq_norm
    : ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        u ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u = ‖u‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨u, huNe, hAction⟩
  refine ⟨u, huNe, ?_⟩
  have hSq :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u
  rw [hAction, real_inner_self_eq_norm_sq] at hSq
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      u
  nlinarith [norm_nonneg u]

/-- Exact primal/dual Green--Poisson energy pairing inequality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    |inner ℝ f u| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u := by
  calc
    |inner ℝ f u| =
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u)| := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_poisson_right]
    _ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_greenEnergyNorm_mul_greenEnergyNorm
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u)
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u := by
      rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson]

/-- The Green--Poisson energy pairing constant one is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm :
    ∃ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      u ≠ 0 ∧
      |inner ℝ f u| =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨u, huNe, hPoisson⟩
  have hGreen :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self
      u
  rw [hPoisson] at hGreen
  have hGreenEnergy :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          u = ‖u‖ := by
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
    rw [hGreen, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg u)]
  have hPoissonEnergy :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u = ‖u‖ := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
    rw [hPoisson, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg u)]
  refine ⟨u, u, huNe, huNe, ?_⟩
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖u‖),
    hGreenEnergy, hPoissonEnergy]
  ring

/-- Any uniform Green--Poisson energy pairing constant is at least one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyDuality_uniform_constant_ge_one
    (C : ℝ)
    (hC :
      ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        |inner ℝ f u| ≤
          C *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u) :
    (1 : ℝ) ≤ C := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm
    with ⟨f, u, hfNe, huNe, hSharp⟩
  have hBound := hC f u
  rw [hSharp] at hBound
  have hGreenPos :
      0 <
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f := by
    have hLower :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_bounds
        f).1
    have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
    nlinarith
  have hPoissonPos :
      0 <
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u := by
    have hLower :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
        u).1
    have hNormPos : 0 < ‖u‖ := norm_pos_iff.mpr huNe
    nlinarith
  let p : ℝ :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f *
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u
  have hpPos : 0 < p := by
    dsimp [p]
    exact mul_pos hGreenPos hPoissonPos
  have hBound' : (1 : ℝ) * p ≤ C * p := by
    dsimp [p]
    calc
      (1 : ℝ) *
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u := by ring
      _ ≤
        C *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u := hBound
      _ =
        C *
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u) := by ring
  have hDiv : (1 : ℝ) ≤ (C * p) / p :=
    (le_div_iff₀ hpPos).2 hBound'
  have hpNe : p ≠ 0 := ne_of_gt hpPos
  simpa [hpNe] using hDiv

/-- Structured receipt for the exact Green/Poisson energy norm geometry and
primal--dual pairing on the actual beta-zero centered sector. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyDualityL2Receipt :
    Prop where
  intrinsic_cauchy_schwarz :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g| ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            g
  green_zero_iff :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f = 0 ↔
        f = 0
  green_smul :
    ∀ (a : ℝ)
      (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (a • f) =
        |a| *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f
  green_triangle :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (f + g) ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            g
  green_bounds :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ‖f‖ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ≤
          18 * ‖f‖
  green_endpoints :
    (∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f = ‖f‖) ∧
    (∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f = 18 * ‖f‖)
  poisson_zero_iff :
    ∀ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u = 0 ↔
        u = 0
  poisson_smul :
    ∀ (a : ℝ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          (a • u) =
        |a| *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u
  poisson_triangle :
    ∀ u v : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          (u + v) ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            v
  poisson_bounds :
    ∀ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ((1 : ℝ) / 18) * ‖u‖ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ≤
          ‖u‖
  poisson_endpoints :
    (∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u = ((1 : ℝ) / 18) * ‖u‖) ∧
    (∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u = ‖u‖)
  exact_duality :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      |inner ℝ f u| ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u
  duality_constant_sharp :
    ∀ C : ℝ,
      (∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        |inner ℝ f u| ≤
          C *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u) →
      (1 : ℝ) ≤ C

/-- The exact beta-zero Green/Poisson energy duality receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyDualityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyDualityL2Receipt := by
  exact
    { intrinsic_cauchy_schwarz :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_greenEnergyNorm_mul_greenEnergyNorm
      green_zero_iff :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
      green_smul :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul
      green_triangle :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_add_le
      green_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_bounds
      green_endpoints := ⟨
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenEnergyNormL2_eq_norm,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenEnergyNormL2_eq_18_mul_norm⟩
      poisson_zero_iff :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
      poisson_smul :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul
      poisson_triangle :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_add_le
      poisson_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
      poisson_endpoints := ⟨
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonEnergyNormL2_eq_inv_18_mul_norm,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonEnergyNormL2_eq_norm⟩
      exact_duality :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
      duality_constant_sharp :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyDuality_uniform_constant_ge_one }

end

end MathlibAnalytic
end MGAP4D
