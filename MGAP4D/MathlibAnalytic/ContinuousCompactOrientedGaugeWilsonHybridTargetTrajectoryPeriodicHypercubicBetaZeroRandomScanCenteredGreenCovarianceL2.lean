import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonGreenRayleighQuotientL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A right inverse of an inner-symmetric continuous linear endomorphism is
inner symmetric. -/
theorem continuousLinearMap_rightInverse_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G : E →L[ℝ] E)
    (hA : ∀ f g : E, inner ℝ (A f) g = inner ℝ f (A g))
    (hAG : ∀ f : E, A (G f) = f)
    (f g : E) :
    inner ℝ (G f) g = inner ℝ f (G g) := by
  calc
    inner ℝ (G f) g = inner ℝ (G f) (A (G g)) := by rw [hAG]
    _ = inner ℝ (A (G f)) (G g) := (hA (G f) (G g)).symm
    _ = inner ℝ f (G g) := by rw [hAG]

/-- The internal beta-zero Poisson endomorphism is inner symmetric on the
actual Gibbs-vacuum orthogonal sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_symm
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          g) := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (g : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The centered Green inverse is inner symmetric on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g) := by
  exact
    continuousLinearMap_rightInverse_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
      f g

/-- The centered Green covariance bilinear form on the actual beta-zero
Gibbs-vacuum orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  inner ℝ
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      f)
    g

/-- The actual centered Green covariance is symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_symm
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        g f := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  calc
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
        f g
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g)
        f := real_inner_comm _ _

/-- Applying the covariance to a Poisson image in its first slot recovers the
ambient inner product. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_poisson_left
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f)
        g =
      inner ℝ f g := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self]

/-- Applying the covariance to a Poisson image in its second slot also recovers
 the ambient inner product. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_poisson_right
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          g) =
      inner ℝ f g := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  calc
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          g) =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f))
        g :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_symm
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        g).symm
    _ = inner ℝ f g := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- The covariance diagonal dominates the squared ambient norm with exact lower
constant one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_le_randomScanCenteredGreenCovarianceL2_self
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖f‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f f := by
  have hCocoercive :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_inner
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        f)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]
    at hCocoercive
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  calc
    ‖f‖ ^ 2 ≤
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f) := hCocoercive
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        f := real_inner_comm _ _

/-- The covariance diagonal is bounded above by `324` times the squared ambient
norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_le_324_mul_norm_sq
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f f ≤
      324 * ‖f‖ ^ 2 := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  have hUpper :=
    continuousLinearMap_inner_apply_self_le_opNorm_mul_norm_sq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      f
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324] using
    hUpper

/-- Exact two-sided covariance-diagonal control on the beta-zero centered
sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_bounds
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖f‖ ^ 2 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f ≤
        324 * ‖f‖ ^ 2 := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_le_randomScanCenteredGreenCovarianceL2_self
      f,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_le_324_mul_norm_sq
      f⟩

/-- The centered Green covariance diagonal is nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_nonneg
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f f := by
  exact le_trans (sq_nonneg ‖f‖)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_le_randomScanCenteredGreenCovarianceL2_self
      f)

/-- The centered Green covariance is positive definite on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_eq_zero_iff
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f f = 0 ↔
      f = 0 := by
  constructor
  · intro hZero
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_le_randomScanCenteredGreenCovarianceL2_self
        f
    rw [hZero] at hLower
    have hNormZero : ‖f‖ = 0 := by
      nlinarith [norm_nonneg f]
    exact norm_eq_zero.mp hNormZero
  · intro hZero
    rw [hZero]
    simp [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2]

/-- Ambient Cauchy--Schwarz and the exact Green operator norm give the sharp
bilinear covariance bound with constant `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_324_mul_norm_mul_norm
    (f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
        f g| ≤
      324 * ‖f‖ * ‖g‖ := by
  have hGreenNorm :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f‖ ≤
        324 * ‖f‖ := by
    calc
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2‖ *
          ‖f‖ :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2.le_opNorm
          f
      _ = 324 * ‖f‖ := by
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  calc
    |inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
        g| ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (324 * ‖f‖) * ‖g‖ :=
      mul_le_mul_of_nonneg_right hGreenNorm (norm_nonneg g)
    _ = 324 * ‖f‖ * ‖g‖ := by ring

/-- A terminal-cardinality mode attains the lower covariance-diagonal constant
one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_norm_sq :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f =
        ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_self
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  rw [hAction, real_inner_self_eq_norm_sq]

/-- A cardinality-one mode attains the upper covariance-diagonal constant
`324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f =
        324 * ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_324_smul
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
  rw [hAction, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The bilinear covariance bound with constant `324` is attained on the
cardinality-one diagonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_abs_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f| =
        324 * ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq
    with ⟨f, hfNe, hDiagonal⟩
  refine ⟨f, hfNe, ?_⟩
  rw [hDiagonal, abs_of_nonneg]
  exact mul_nonneg (by norm_num) (sq_nonneg ‖f‖)

/-- Any uniform bilinear covariance constant is at least `324`; hence the
proved constant is exact. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_uniform_bilinear_constant_ge_324
    (C : ℝ)
    (hC :
      ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f g| ≤
          C * ‖f‖ * ‖g‖) :
    (324 : ℝ) ≤ C := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_abs_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq
    with ⟨f, hfNe, hSharp⟩
  have hBound := hC f f
  have hBound' :
      (324 : ℝ) * ‖f‖ ^ 2 ≤
        C * ‖f‖ ^ 2 := by
    calc
      (324 : ℝ) * ‖f‖ ^ 2 =
          |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f f| := hSharp.symm
      _ ≤ C * ‖f‖ * ‖f‖ := hBound
      _ = C * ‖f‖ ^ 2 := by ring
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  have hSqPos : 0 < ‖f‖ ^ 2 := sq_pos_of_pos hNormPos
  nlinarith

/-- Structured receipt for the actual beta-zero centered Green covariance
geometry and its exact bilinear constant. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2Receipt :
    Prop where
  symmetric :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          g f
  poisson_left :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            f)
          g =
        inner ℝ f g
  poisson_right :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            g) =
        inner ℝ f g
  diagonal_bounds :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ‖f‖ ^ 2 ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f f ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f f ≤
          324 * ‖f‖ ^ 2
  positive_definite :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f = 0 ↔
        f = 0
  bilinear_bound :
    ∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f g| ≤
        324 * ‖f‖ * ‖g‖
  lower_diagonal_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f =
        ‖f‖ ^ 2
  upper_diagonal_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f =
        324 * ‖f‖ ^ 2
  bilinear_constant_sharp :
    ∀ C : ℝ,
      (∀ f g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
            f g| ≤
          C * ‖f‖ * ‖g‖) →
      (324 : ℝ) ≤ C

/-- The exact beta-zero centered Green covariance receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2Receipt := by
  exact
    { symmetric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_symm
      poisson_left :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_poisson_left
      poisson_right :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_poisson_right
      diagonal_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_bounds
      positive_definite :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_self_eq_zero_iff
      bilinear_bound :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanCenteredGreenCovarianceL2_le_324_mul_norm_mul_norm
      lower_diagonal_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_norm_sq
      upper_diagonal_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenCovarianceL2_self_eq_324_mul_norm_sq
      bilinear_constant_sharp :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenCovarianceL2_uniform_bilinear_constant_ge_324 }

end

end MathlibAnalytic
end MGAP4D
