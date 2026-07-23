import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonEnergyDualityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic Poisson--Green square completion for a symmetric continuous
endomorphism and a right inverse. -/
theorem continuousLinearMap_poissonGreen_square_completion
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G : E →L[ℝ] E)
    (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hAG : ∀ x : E, A (G x) = x)
    (f u : E) :
    inner ℝ (A (u - G f)) (u - G f) =
      inner ℝ (A u) u - 2 * inner ℝ f u + inner ℝ (G f) f := by
  have hCross₁ : inner ℝ (A u) (G f) = inner ℝ f u := by
    calc
      inner ℝ (A u) (G f) = inner ℝ u (A (G f)) := hA u (G f)
      _ = inner ℝ u f := by rw [hAG]
      _ = inner ℝ f u := real_inner_comm _ _
  have hCross₂ : inner ℝ (A (G f)) u = inner ℝ f u := by
    rw [hAG]
  have hLast : inner ℝ (A (G f)) (G f) = inner ℝ (G f) f := by
    rw [hAG, real_inner_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hCross₁, hCross₂, hLast]
  ring

/-- Generic Green--Poisson square completion for a symmetric continuous right
inverse. -/
theorem continuousLinearMap_greenPoisson_square_completion
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G : E →L[ℝ] E)
    (hG : ∀ x y : E, inner ℝ (G x) y = inner ℝ x (G y))
    (hGA : ∀ x : E, G (A x) = x)
    (f u : E) :
    inner ℝ (G (f - A u)) (f - A u) =
      inner ℝ (G f) f - 2 * inner ℝ f u + inner ℝ (A u) u := by
  have hCross₁ : inner ℝ (G f) (A u) = inner ℝ f u := by
    calc
      inner ℝ (G f) (A u) = inner ℝ f (G (A u)) := hG f (A u)
      _ = inner ℝ f u := by rw [hGA]
  have hCross₂ : inner ℝ (G (A u)) f = inner ℝ f u := by
    rw [hGA, real_inner_comm]
  have hLast : inner ℝ (G (A u)) (A u) = inner ℝ (A u) u := by
    rw [hGA]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hCross₁, hCross₂, hLast]
  ring

/-- Exact Poisson-energy square completion around the canonical centered Green
solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sub_centeredGreen_sq
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          (u -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f) ^ 2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 -
        2 * inner ℝ f u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          (u -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f) ^ 2 =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (u -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              f))
        (u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
        _
    _ =
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u)
          u -
        2 * inner ℝ f u +
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f :=
      continuousLinearMap_poissonGreen_square_completion
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_symm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
        f u
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 -
        2 * inner ℝ f u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 := by
      rw [
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq]
      rfl

/-- Exact Green-energy square completion around the Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sub_poisson_sq
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              u) ^ 2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 -
        2 * inner ℝ f u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          (f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              u) ^ 2 =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          (f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              u))
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq]
      rfl
    _ =
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f -
        2 * inner ℝ f u +
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u)
          u :=
      continuousLinearMap_greenPoisson_square_completion
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self
        f u
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 -
        2 * inner ℝ f u +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq,
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq]
      rfl

/-- The concave Poisson-side Fenchel value. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  inner ℝ f u -
    ((1 : ℝ) / 2) *
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ^ 2

/-- The concave Green-side Fenchel value. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
    (u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  inner ℝ f u -
    ((1 : ℝ) / 2) *
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ^ 2

/-- Exact Poisson-side Fenchel gap as a squared canonical-solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2 -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
          f u =
      ((1 : ℝ) / 2) *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            (u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f) ^ 2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sub_centeredGreen_sq]
  ring

/-- Exact Green-side Fenchel gap as a squared Poisson-image error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
    (u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2 -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
          u f =
      ((1 : ℝ) / 2) *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                u) ^ 2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sub_poisson_sq]
  ring

/-- Poisson-side Fenchel upper bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_le_half_green_sq
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
        f u ≤
      ((1 : ℝ) / 2) *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
      f u
  have hNonneg :
      0 ≤
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              (u -
                periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                  f) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

/-- Green-side Fenchel upper bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_le_half_poisson_sq
    (u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
        u f ≤
      ((1 : ℝ) / 2) *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
      u f
  have hNonneg :
      0 ≤
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              (f -
                periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                  u) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

/-- The Poisson-side Fenchel upper bound is attained exactly at the canonical
centered Green solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_eq_half_green_sq_iff
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
          f u =
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2 ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f := by
  constructor
  · intro hEq
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
        f u
    have hEnergyNonneg :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        (u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
    have hEnergyZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            (u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f) = 0 := by
      nlinarith
    exact sub_eq_zero.mp
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        _).1 hEnergyZero)
  · intro hCanonical
    rw [hCanonical]
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f)
    have hEnergyZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f) = 0 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        _).2 (sub_self _)
    rw [hEnergyZero] at hGap
    nlinarith

/-- The Green-side Fenchel upper bound is attained exactly at the Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_eq_half_poisson_sq_iff
    (u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
          u f =
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2 ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u := by
  constructor
  · intro hEq
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
        u f
    have hEnergyNonneg :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u)
    have hEnergyZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                u) = 0 := by
      nlinarith
    exact sub_eq_zero.mp
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        _).1 hEnergyZero)
  · intro hCanonical
    rw [hCanonical]
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
        u
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u)
    have hEnergyZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                u) = 0 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        _).2 (sub_self _)
    rw [hEnergyZero] at hGap
    nlinarith

/-- Symmetric Fenchel--Young inequality in the exact energy norms. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_half_green_sq_add_poisson_sq
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    |inner ℝ f u| ≤
      ((1 : ℝ) / 2) *
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2 +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2) := by
  have hDual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
      f u
  have hSquare :
      0 ≤
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u) ^ 2 := sq_nonneg _
  nlinarith

/-- Poisson energy of the centered Green image equals Green energy of the source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- Green energy of a Poisson image equals Poisson energy of the source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_poisson_eq_poissonEnergyNorm
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson
    u).symm

/-- Green energy is strictly positive exactly on nonzero vectors. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_iff
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ↔
      f ≠ 0 := by
  constructor
  · intro hPos hZero
    have hEnergyZero :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        f).2 hZero
    exact (ne_of_gt hPos) hEnergyZero
  · intro hNe
    have hEnergyNe :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ≠ 0 := by
      intro hZero
      exact hNe
        ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
          f).1 hZero)
    exact lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
      (Ne.symm hEnergyNe)

/-- Poisson energy is strictly positive exactly on nonzero vectors. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_iff
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ↔
      u ≠ 0 := by
  constructor
  · intro hPos hZero
    have hEnergyZero :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        u).2 hZero
    exact (ne_of_gt hPos) hEnergyZero
  · intro hNe
    have hEnergyNe :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ≠ 0 := by
      intro hZero
      exact hNe
        ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
          u).1 hZero)
    exact lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        u)
      (Ne.symm hEnergyNe)

/-- Canonical Poisson-energy unit witness for the Green dual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
      f)⁻¹ •
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      f

/-- The Green dual witness has unit Poisson energy for every nonzero source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hf : f ≠ 0) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f) = 1 := by
  have hPos :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_iff
      f).2 hf
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul,
    abs_of_pos (inv_pos.mpr hPos),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm]
  exact inv_mul_cancel₀ (ne_of_gt hPos)

/-- The Green dual witness attains the Green energy exactly. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hf : f ≠ 0) :
    |inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f)| =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f := by
  have hPos :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_iff
      f).2 hf
  have hInner :
      inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 := by
    calc
      inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f) =
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f := real_inner_comm _ _
      _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2
          f f := rfl
      _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f ^ 2 :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
          f).symm
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  rw [real_inner_smul_right, hInner]
  have hCancel :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f)⁻¹ *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2 =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f := by
    field_simp [ne_of_gt hPos]
  rw [hCancel, abs_of_pos hPos]

/-- Every Poisson-energy unit vector is bounded by the Green energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hu :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ≤ 1) :
    |inner ℝ f u| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f := by
  calc
    |inner ℝ f u| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
        f u
    _ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f * 1 :=
      mul_le_mul_of_nonneg_left hu
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
          f)
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        f := by ring

/-- Canonical Green-energy unit witness for the Poisson dual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
      u)⁻¹ •
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      u

/-- The Poisson dual witness has unit Green energy for every nonzero source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hu : u ≠ 0) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u) = 1 := by
  have hPos :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_iff
      u).2 hu
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul,
    abs_of_pos (inv_pos.mpr hPos),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_poisson_eq_poissonEnergyNorm]
  exact inv_mul_cancel₀ (ne_of_gt hPos)

/-- The Poisson dual witness attains the Poisson energy exactly. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hu : u ≠ 0) :
    |inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u)
        u| =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u := by
  have hPos :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_iff
      u).2 hu
  have hInner :
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u)
          u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u ^ 2 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u).symm
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  rw [real_inner_smul_left, hInner]
  have hCancel :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u)⁻¹ *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2 =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u := by
    field_simp [ne_of_gt hPos]
  rw [hCancel, abs_of_pos hPos]

/-- Every Green-energy unit vector is bounded by the Poisson energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
    (f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hf :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ≤ 1) :
    |inner ℝ f u| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u := by
  calc
    |inner ℝ f u| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
        f u
    _ ≤
      1 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u :=
      mul_le_mul_of_nonneg_right hf
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
          u)
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
        u := by ring

/-- Structured receipt for exact beta-zero Green--Poisson Fenchel duality and
its two explicit dual-norm witnesses. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonFenchelDualityL2Receipt :
    Prop where
  poisson_square_completion :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            (u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
                f) ^ 2 =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2 -
          2 * inner ℝ f u +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2
  green_square_completion :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
                u) ^ 2 =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2 -
          2 * inner ℝ f u +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2
  fenchel_young :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      |inner ℝ f u| ≤
        ((1 : ℝ) / 2) *
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
                f ^ 2 +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
                u ^ 2)
  poisson_fenchel_upper :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
          f u ≤
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f ^ 2
  poisson_fenchel_equality :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
            f u =
          ((1 : ℝ) / 2) *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
                f ^ 2 ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f
  green_fenchel_upper :
    ∀ u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
          u f ≤
        ((1 : ℝ) / 2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u ^ 2
  green_fenchel_equality :
    ∀ u f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
            u f =
          ((1 : ℝ) / 2) *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
                u ^ 2 ↔
        f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u
  green_dual_upper :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
          u ≤ 1 →
        |inner ℝ f u| ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            f
  green_dual_attained :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 →
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
              f) = 1 ∧
          |inner ℝ f
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
                f)| =
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
              f
  poisson_dual_upper :
    ∀ f u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
          f ≤ 1 →
        |inner ℝ f u| ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
            u
  poisson_dual_attained :
    ∀ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 →
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
              u) = 1 ∧
          |inner ℝ
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
                u)
              u| =
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
              u

/-- The exact beta-zero Green--Poisson Fenchel-duality receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonFenchelDualityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonFenchelDualityL2Receipt := by
  exact
    { poisson_square_completion :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sub_centeredGreen_sq
      green_square_completion :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sub_poisson_sq
      fenchel_young :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_half_green_sq_add_poisson_sq
      poisson_fenchel_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_le_half_green_sq
      poisson_fenchel_equality :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_eq_half_green_sq_iff
      green_fenchel_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_le_half_poisson_sq
      green_fenchel_equality :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_eq_half_poisson_sq_iff
      green_dual_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
      green_dual_attained := by
        intro f hf
        exact ⟨
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
            f hf,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
            f hf⟩
      poisson_dual_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
      poisson_dual_attained := by
        intro u hu
        exact ⟨
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
            u hu,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
            u hu⟩ }

end

end MathlibAnalytic
end MGAP4D
