import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonEnergyDualityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "H₀" =>
  Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
local notation "A₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "GE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
local notation "PE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
local notation "B₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenCovarianceL2

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
    rw [hGA, real_inner_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hCross₁, hCross₂, hLast]
  ring

/-- Exact Poisson-energy square completion around the canonical centered Green
solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sub_centeredGreen_sq
    (f u : Ω₀) :
    PE₀ (u - G₀ f) ^ 2 =
      PE₀ u ^ 2 - 2 * inner ℝ f u + GE₀ f ^ 2 := by
  calc
    PE₀ (u - G₀ f) ^ 2 = inner ℝ (A₀ (u - G₀ f)) (u - G₀ f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq _
    _ = inner ℝ (A₀ u) u - 2 * inner ℝ f u + inner ℝ (G₀ f) f :=
      continuousLinearMap_poissonGreen_square_completion
        A₀ G₀
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_inner_symm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
        f u
    _ = PE₀ u ^ 2 - 2 * inner ℝ f u + GE₀ f ^ 2 := by
      rw [
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq]
      rfl

/-- Exact Green-energy square completion around the Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sub_poisson_sq
    (f u : Ω₀) :
    GE₀ (f - A₀ u) ^ 2 =
      GE₀ f ^ 2 - 2 * inner ℝ f u + PE₀ u ^ 2 := by
  calc
    GE₀ (f - A₀ u) ^ 2 = inner ℝ (G₀ (f - A₀ u)) (f - A₀ u) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq]
      rfl
    _ = inner ℝ (G₀ f) f - 2 * inner ℝ f u + inner ℝ (A₀ u) u :=
      continuousLinearMap_greenPoisson_square_completion
        A₀ G₀
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_inner_symm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self
        f u
    _ = GE₀ f ^ 2 - 2 * inner ℝ f u + PE₀ u ^ 2 := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq,
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq]
      rfl

/-- The concave Poisson-side Fenchel value. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
    (f u : Ω₀) : ℝ :=
  inner ℝ f u - ((1 : ℝ) / 2) * PE₀ u ^ 2

/-- The concave Green-side Fenchel value. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
    (u f : Ω₀) : ℝ :=
  inner ℝ f u - ((1 : ℝ) / 2) * GE₀ f ^ 2

/-- Exact Poisson-side Fenchel gap as a squared canonical-solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
    (f u : Ω₀) :
    ((1 : ℝ) / 2) * GE₀ f ^ 2 -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2 f u =
      ((1 : ℝ) / 2) * PE₀ (u - G₀ f) ^ 2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sub_centeredGreen_sq]
  ring

/-- Exact Green-side Fenchel gap as a squared Poisson-image error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
    (u f : Ω₀) :
    ((1 : ℝ) / 2) * PE₀ u ^ 2 -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2 u f =
      ((1 : ℝ) / 2) * GE₀ (f - A₀ u) ^ 2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sub_poisson_sq]
  ring

/-- Poisson-side Fenchel upper bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_le_half_green_sq
    (f u : Ω₀) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2 f u ≤
      ((1 : ℝ) / 2) * GE₀ f ^ 2 := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq f u
  have hNonneg : 0 ≤ ((1 : ℝ) / 2) * PE₀ (u - G₀ f) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

/-- Green-side Fenchel upper bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_le_half_poisson_sq
    (u f : Ω₀) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2 u f ≤
      ((1 : ℝ) / 2) * PE₀ u ^ 2 := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq u f
  have hNonneg : 0 ≤ ((1 : ℝ) / 2) * GE₀ (f - A₀ u) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

/-- The Poisson-side Fenchel upper bound is attained exactly at the canonical
centered Green solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelValueL2_eq_half_green_sq_iff
    (f u : Ω₀) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2 f u =
        ((1 : ℝ) / 2) * GE₀ f ^ 2 ↔
      u = G₀ f := by
  constructor
  · intro hEq
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq f u
    have hEnergyNonneg :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        (u - G₀ f)
    have hEnergyZero : PE₀ (u - G₀ f) = 0 := by
      nlinarith
    exact sub_eq_zero.mp
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        _).1 hEnergyZero)
  · intro hCanonical
    rw [hCanonical]
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq
        f (G₀ f)
    have hEnergyZero : PE₀ (G₀ f - G₀ f) = 0 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        _).2 (sub_self _)
    rw [hEnergyZero] at hGap
    nlinarith

/-- The Green-side Fenchel upper bound is attained exactly at the Poisson image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelValueL2_eq_half_poisson_sq_iff
    (u f : Ω₀) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2 u f =
        ((1 : ℝ) / 2) * PE₀ u ^ 2 ↔
      f = A₀ u := by
  constructor
  · intro hEq
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq u f
    have hEnergyNonneg :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        (f - A₀ u)
    have hEnergyZero : GE₀ (f - A₀ u) = 0 := by
      nlinarith
    exact sub_eq_zero.mp
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        _).1 hEnergyZero)
  · intro hCanonical
    rw [hCanonical]
    have hGap :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenFenchelGapL2_eq_half_error_sq
        u (A₀ u)
    have hEnergyZero : GE₀ (A₀ u - A₀ u) = 0 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        _).2 (sub_self _)
    rw [hEnergyZero] at hGap
    nlinarith

/-- Symmetric Fenchel--Young inequality in the exact energy norms. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_half_green_sq_add_poisson_sq
    (f u : Ω₀) :
    |inner ℝ f u| ≤ ((1 : ℝ) / 2) * (GE₀ f ^ 2 + PE₀ u ^ 2) := by
  have hDual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
      f u
  have hSquare : 0 ≤ (GE₀ f - PE₀ u) ^ 2 := sq_nonneg _
  nlinarith

/-- Poisson energy of the centered Green image equals Green energy of the source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm
    (f : Ω₀) :
    PE₀ (G₀ f) = GE₀ f := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- Green energy of a Poisson image equals Poisson energy of the source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_poisson_eq_poissonEnergyNorm
    (u : Ω₀) :
    GE₀ (A₀ u) = PE₀ u :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_greenEnergyNorm_poisson
    u).symm

/-- Canonical Poisson-energy unit witness for the Green dual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
    (f : Ω₀) : Ω₀ :=
  (GE₀ f)⁻¹ • G₀ f

/-- The Green dual witness has unit Poisson energy for every nonzero source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
    (f : Ω₀)
    (hf : f ≠ 0) :
    PE₀
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f) = 1 := by
  have hEnergyNe : GE₀ f ≠ 0 := by
    intro hZero
    exact hf
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        f).1 hZero)
  have hPos : 0 < GE₀ f :=
    lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
      (Ne.symm hEnergyNe)
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul,
    abs_of_pos (inv_pos.mpr hPos),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm]
  exact inv_mul_cancel₀ hEnergyNe

/-- The Green dual witness attains the Green energy exactly. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_greenDualUnitWitnessL2_eq_greenEnergyNorm
    (f : Ω₀)
    (hf : f ≠ 0) :
    |inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
          f)| = GE₀ f := by
  have hEnergyNe : GE₀ f ≠ 0 := by
    intro hZero
    exact hf
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        f).1 hZero)
  have hPos : 0 < GE₀ f :=
    lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
      (Ne.symm hEnergyNe)
  have hInner :
      inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) = GE₀ f ^ 2 := by
    calc
      inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) =
          inner ℝ ((G₀ f : Ω₀) : H₀) (f : H₀) := real_inner_comm _ _
      _ = B₀ f f := rfl
      _ = GE₀ f ^ 2 :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
          f).symm
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  change
    |inner ℝ (f : H₀) ((GE₀ f)⁻¹ • ((G₀ f : Ω₀) : H₀))| = GE₀ f
  rw [real_inner_smul_right, hInner]
  have hCancel : (GE₀ f)⁻¹ * GE₀ f ^ 2 = GE₀ f := by
    field_simp [hEnergyNe]
  rw [hCancel, abs_of_pos hPos]

/-- Every Poisson-energy unit vector is bounded by the Green energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_of_poissonEnergy_le_one
    (f u : Ω₀)
    (hu : PE₀ u ≤ 1) :
    |inner ℝ f u| ≤ GE₀ f := by
  calc
    |inner ℝ f u| ≤ GE₀ f * PE₀ u :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
        f u
    _ ≤ GE₀ f * 1 :=
      mul_le_mul_of_nonneg_left hu
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
          f)
    _ = GE₀ f := by ring

/-- Canonical Green-energy unit witness for the Poisson dual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
    (u : Ω₀) : Ω₀ :=
  (PE₀ u)⁻¹ • A₀ u

/-- The Poisson dual witness has unit Green energy for every nonzero source. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
    (u : Ω₀)
    (hu : u ≠ 0) :
    GE₀
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u) = 1 := by
  have hEnergyNe : PE₀ u ≠ 0 := by
    intro hZero
    exact hu
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        u).1 hZero)
  have hPos : 0 < PE₀ u :=
    lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        u)
      (Ne.symm hEnergyNe)
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul,
    abs_of_pos (inv_pos.mpr hPos),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_poisson_eq_poissonEnergyNorm]
  exact inv_mul_cancel₀ hEnergyNe

/-- The Poisson dual witness attains the Poisson energy exactly. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_poissonDualUnitWitnessL2_eq_poissonEnergyNorm
    (u : Ω₀)
    (hu : u ≠ 0) :
    |inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
          u)
        u| = PE₀ u := by
  have hEnergyNe : PE₀ u ≠ 0 := by
    intro hZero
    exact hu
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        u).1 hZero)
  have hPos : 0 < PE₀ u :=
    lt_of_le_of_ne
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        u)
      (Ne.symm hEnergyNe)
  have hInner :
      inner ℝ ((A₀ u : Ω₀) : H₀) (u : H₀) = PE₀ u ^ 2 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u).symm
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  change
    |inner ℝ ((PE₀ u)⁻¹ • ((A₀ u : Ω₀) : H₀)) (u : H₀)| = PE₀ u
  rw [real_inner_smul_left, hInner]
  have hCancel : (PE₀ u)⁻¹ * PE₀ u ^ 2 = PE₀ u := by
    field_simp [hEnergyNe]
  rw [hCancel, abs_of_pos hPos]

/-- Every Green-energy unit vector is bounded by the Poisson energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_poissonEnergyNorm_of_greenEnergy_le_one
    (f u : Ω₀)
    (hf : GE₀ f ≤ 1) :
    |inner ℝ f u| ≤ PE₀ u := by
  calc
    |inner ℝ f u| ≤ GE₀ f * PE₀ u :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_le_greenEnergyNorm_mul_poissonEnergyNorm
        f u
    _ ≤ 1 * PE₀ u :=
      mul_le_mul_of_nonneg_right hf
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
          u)
    _ = PE₀ u := by ring

/-- Structured receipt for exact beta-zero Green--Poisson Fenchel duality and
its two explicit dual-norm witnesses. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonFenchelDualityL2Receipt :
    Prop where
  poisson_square_completion :
    ∀ f u : Ω₀,
      PE₀ (u - G₀ f) ^ 2 = PE₀ u ^ 2 - 2 * inner ℝ f u + GE₀ f ^ 2
  green_square_completion :
    ∀ f u : Ω₀,
      GE₀ (f - A₀ u) ^ 2 = GE₀ f ^ 2 - 2 * inner ℝ f u + PE₀ u ^ 2
  fenchel_young :
    ∀ f u : Ω₀,
      |inner ℝ f u| ≤ ((1 : ℝ) / 2) * (GE₀ f ^ 2 + PE₀ u ^ 2)
  poisson_fenchel_upper :
    ∀ f u : Ω₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
          f u ≤ ((1 : ℝ) / 2) * GE₀ f ^ 2
  poisson_fenchel_equality :
    ∀ f u : Ω₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
            f u = ((1 : ℝ) / 2) * GE₀ f ^ 2 ↔
        u = G₀ f
  green_fenchel_upper :
    ∀ u f : Ω₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
          u f ≤ ((1 : ℝ) / 2) * PE₀ u ^ 2
  green_fenchel_equality :
    ∀ u f : Ω₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenFenchelValueL2
            u f = ((1 : ℝ) / 2) * PE₀ u ^ 2 ↔
        f = A₀ u
  green_dual_upper :
    ∀ f u : Ω₀, PE₀ u ≤ 1 → |inner ℝ f u| ≤ GE₀ f
  green_dual_attained :
    ∀ f : Ω₀, f ≠ 0 →
      PE₀
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
            f) = 1 ∧
        |inner ℝ f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
              f)| = GE₀ f
  poisson_dual_upper :
    ∀ f u : Ω₀, GE₀ f ≤ 1 → |inner ℝ f u| ≤ PE₀ u
  poisson_dual_attained :
    ∀ u : Ω₀, u ≠ 0 →
      GE₀
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
            u) = 1 ∧
        |inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
              u)
            u| = PE₀ u

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
