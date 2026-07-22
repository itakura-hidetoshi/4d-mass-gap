import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonMoorePenroseBlockL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A projected inverse of an inner-symmetric operator is inner symmetric when
both the projection and the inverse range are compatible with the projection. -/
theorem continuousLinearMap_projectedInverse_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G C : E →L[ℝ] E)
    (hA : ∀ f g : E, inner ℝ (A f) g = inner ℝ f (A g))
    (hC : ∀ f g : E, inner ℝ (C f) g = inner ℝ f (C g))
    (hAG : ∀ f : E, A (G f) = C f)
    (hCG : ∀ f : E, C (G f) = G f)
    (f g : E) :
    inner ℝ (G f) g = inner ℝ f (G g) := by
  calc
    inner ℝ (G f) g = inner ℝ (C (G f)) g := by rw [hCG]
    _ = inner ℝ (G f) (C g) := hC (G f) g
    _ = inner ℝ (G f) (A (G g)) := by rw [hAG]
    _ = inner ℝ (A (G f)) (G g) := (hA (G f) (G g)).symm
    _ = inner ℝ (C f) (G g) := by rw [hAG]
    _ = inner ℝ f (C (G g)) := hC f (G g)
    _ = inner ℝ f (G g) := by rw [hCG]

/-- The quadratic form of a compatible projected inverse is the original
operator quadratic form evaluated on the canonical inverse image. -/
theorem continuousLinearMap_projectedInverse_quadraticForm_eq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G C : E →L[ℝ] E)
    (hA : ∀ f g : E, inner ℝ (A f) g = inner ℝ f (A g))
    (hC : ∀ f g : E, inner ℝ (C f) g = inner ℝ f (C g))
    (hAG : ∀ f : E, A (G f) = C f)
    (hCG : ∀ f : E, C (G f) = G f)
    (f : E) :
    inner ℝ (G f) f = inner ℝ (A (G f)) (G f) := by
  calc
    inner ℝ (G f) f = inner ℝ (C (G f)) f := by rw [hCG]
    _ = inner ℝ (G f) (C f) := hC (G f) f
    _ = inner ℝ (G f) (A (G f)) := by rw [hAG]
    _ = inner ℝ (A (G f)) (G f) := (hA (G f) (G f)).symm

/-- The actual beta-zero Poisson operator is inner symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          g) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
    inner_sub_left, inner_sub_right,
    ContinuousCompactRandomScanL2Structure.continuous_compact_oriented_randomScanHeatBathL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_pos]

/-- Exact quadratic-form expansion of the actual beta-zero Poisson operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f =
      ‖f‖ ^ 2 -
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            f)
          f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
    inner_sub_left, real_inner_self_eq_norm_sq]

/-- The actual beta-zero Poisson quadratic form is nonnegative on the full
ambient Gibbs `L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_nonneg
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    0 ≤ inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f)
      f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm]
  have hUpper :=
    ContinuousCompactRandomScanL2Structure.continuous_compact_oriented_randomScanHeatBathL2_quadraticForm_le_norm_sq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_pos
      f
  linarith

/-- The actual beta-zero Poisson quadratic form is bounded above by the squared
ambient norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm_le_norm_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f ≤
      ‖f‖ ^ 2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm]
  have hNonneg :=
    ContinuousCompactRandomScanL2Structure.continuous_compact_oriented_randomScanHeatBathL2_nonneg
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_pos
      f
  linarith

/-- The Poisson quadratic form has the sharp lower bound `1 / 324` on the
actual Gibbs-vacuum orthogonal sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ((1 : ℝ) / 324) * ‖f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm]
  have hContraction :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanHeatBathL2_apply_le_slem_mul_norm_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hSLEM :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 =
        (323 : ℝ) / 324 := by
    norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]
  rw [hSLEM] at hContraction
  have hCauchy :
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            f)
          f ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            f‖ * ‖f‖ :=
    le_trans (le_abs_self _)
      (abs_real_inner_le_norm
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          f)
        f)
  have hScaled :=
    mul_le_mul_of_nonneg_right hContraction (norm_nonneg f)
  nlinarith [norm_nonneg f]

/-- The sharp quadratic-form lower constant `1 / 324` is attained by a
nonzero cardinality-one mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_quadraticForm_eq_inv_324_mul_norm_sq :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)
          f =
        ((1 : ℝ) / 324) * ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨f, hfNe, hfOrthogonal, hPoisson⟩
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  rw [hPoisson, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Pointwise form of `A G† = C`, with ambient centering on the right. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- Ambient centering fixes the range of the generalized inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_generalizedInverse_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    hOrthogonal, zero_smul, sub_zero]

/-- The ambient beta-zero Moore--Penrose generalized inverse is itself inner
symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_inner_symm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          g) := by
  exact
    continuousLinearMap_projectedInverse_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_generalizedInverse_eq_self
      f g

/-- The generalized-inverse quadratic form is exactly the Poisson energy of the
canonical minimum-norm solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_poissonEnergy
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) := by
  exact
    continuousLinearMap_projectedInverse_quadraticForm_eq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_generalizedInverse_eq_self
      f

/-- The ambient beta-zero Moore--Penrose generalized inverse has a nonnegative
quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_nonneg
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    0 ≤ inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_poissonEnergy]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)

/-- The generalized-inverse quadratic form controls the squared norm of the
canonical solution with the sharp Poisson factor `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_generalizedInverse_sq_le_generalizedInverse_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ((1 : ℝ) / 324) *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)
  calc
    ((1 : ℝ) / 324) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f))
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        hOrthogonal
    _ = inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_poissonEnergy
        f).symm

/-- The generalized-inverse quadratic form vanishes exactly when the canonical
solution vanishes. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_apply_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f = 0 := by
  constructor
  · intro hQuadratic
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_generalizedInverse_sq_le_generalizedInverse_quadraticForm
        f
    rw [hQuadratic] at hLower
    have hNormZero :
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ = 0 := by
      nlinarith [
        norm_nonneg
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)]
    exact norm_eq_zero.mp hNormZero
  · intro hApply
    rw [hApply]
    simp

/-- The generalized-inverse quadratic form vanishes exactly when the datum has
zero vacuum-orthogonal component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_centering_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f = 0 := by
  constructor
  · intro hQuadratic
    have hApply :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_apply_eq_zero
        f).1 hQuadratic
    have hAG :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f
    rw [hApply, map_zero] at hAG
    exact hAG.symm
  · intro hCentering
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_apply_eq_zero
        f).2
    have hAG :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)) :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
          f).symm
      _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) := by
        rw [hAG]
      _ = 0 := by rw [hCentering, map_zero]

/-- Equivalently, the generalized-inverse quadratic form vanishes exactly on
the Gibbs-vacuum line. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_eq_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f = 0 ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_centering_eq_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
    sub_eq_zero]

/-- Structured receipt for self-adjointness and positivity of the actual
beta-zero Poisson Moore--Penrose pair. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenrosePositiveL2Receipt :
    Prop where
  poisson_inner_symm :
    ∀ f g : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)
          g =
        inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            g)
  poisson_nonneg :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      0 ≤ inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f
  poisson_sharp_quadratic_lower :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 →
      ((1 : ℝ) / 324) * ‖f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)
          f
  generalized_inverse_inner_symm :
    ∀ f g : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          g =
        inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            g)
  generalized_inverse_nonneg :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      0 ≤ inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f
  generalized_inverse_energy_lower :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ((1 : ℝ) / 324) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f
  generalized_inverse_quadratic_kernel :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f = 0 ↔
        f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f

/-- The exact self-adjoint positive Moore--Penrose receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenrosePositiveL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenrosePositiveL2Receipt := by
  refine
    { poisson_inner_symm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      poisson_nonneg :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_nonneg
      poisson_sharp_quadratic_lower :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
      generalized_inverse_inner_symm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_inner_symm
      generalized_inverse_nonneg :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_nonneg
      generalized_inverse_energy_lower :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_generalizedInverse_sq_le_generalizedInverse_quadraticForm
      generalized_inverse_quadratic_kernel :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_quadraticForm_eq_zero_iff_eq_vacuumProjector }

end

end MathlibAnalytic
end MGAP4D
