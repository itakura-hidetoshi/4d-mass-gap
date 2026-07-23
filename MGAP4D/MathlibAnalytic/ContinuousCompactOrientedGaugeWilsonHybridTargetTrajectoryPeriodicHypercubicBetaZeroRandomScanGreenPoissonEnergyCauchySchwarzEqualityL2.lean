import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonEnergyUnitSphereDualityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Rescaling by a nonzero real scalar converts an inverse-scaled equality into
an ordinary scaled equality, and conversely. -/
theorem inv_smul_eq_iff_eq_smul_of_ne
    {E : Type*}
    [AddCommGroup E]
    [Module ℝ E]
    (a : ℝ)
    (ha : a ≠ 0)
    (x y : E) :
    a⁻¹ • x = y ↔ x = a • y := by
  constructor
  · intro h
    have hScaled := congrArg (fun z : E => a • z) h
    simpa [smul_smul, ha] using hScaled
  · intro h
    have hScaled := congrArg (fun z : E => a⁻¹ • z) h
    simpa [smul_smul, ha] using hScaled

/-- For a nonnegative target, an absolute-value equality is exactly the two
signed scalar equalities. -/
theorem abs_eq_iff_eq_or_eq_neg_of_nonneg
    (x c : ℝ)
    (hc : 0 ≤ c) :
    |x| = c ↔ x = c ∨ x = -c := by
  constructor
  · intro h
    by_cases hx : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx] using h
    · right
      have hxlt : x < 0 := lt_of_not_ge hx
      have hneg : -x = c := by
        simpa [abs_of_neg hxlt] using h
      linarith
  · rintro (rfl | rfl)
    · exact abs_of_nonneg hc
    · simpa [abs_of_nonneg hc]

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
local notation "GW₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
local notation "PW₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2

/-- The positive Green ray point with the Poisson energy of `u`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPositiveCauchySchwarzRayPointL2
    (f u : Ω₀) : Ω₀ :=
  (PE₀ u * (GE₀ f)⁻¹) • G₀ f

/-- The positive Poisson ray point with the Green energy of `f`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonPositiveCauchySchwarzRayPointL2
    (f u : Ω₀) : Ω₀ :=
  (GE₀ f * (PE₀ u)⁻¹) • A₀ u

local notation "GR₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPositiveCauchySchwarzRayPointL2
local notation "PR₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonPositiveCauchySchwarzRayPointL2

/-- Nonzero data have strictly positive Green energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_of_ne_zero
    (f : Ω₀)
    (hf : f ≠ 0) :
    0 < GE₀ f := by
  have hNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
      f
  have hNe : GE₀ f ≠ 0 := by
    intro hZero
    exact hf
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
        f).1 hZero)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Nonzero states have strictly positive Poisson energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_of_ne_zero
    (u : Ω₀)
    (hu : u ≠ 0) :
    0 < PE₀ u := by
  have hNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      u
  have hNe : PE₀ u ≠ 0 := by
    intro hZero
    exact hu
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
        u).1 hZero)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Green energy is invariant under sign reversal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_neg
    (f : Ω₀) :
    GE₀ (-f) = GE₀ f := by
  simpa using
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul
      (-1 : ℝ) f)

/-- Poisson energy is invariant under sign reversal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_neg
    (u : Ω₀) :
    PE₀ (-u) = PE₀ u := by
  simpa using
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul
      (-1 : ℝ) u)

/-- The source--Green-image pairing is exactly the squared Green energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_centeredGreen_eq_greenEnergyNorm_sq
    (f : Ω₀) :
    inner ℝ f (G₀ f) = GE₀ f ^ 2 := by
  change inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) = GE₀ f ^ 2
  calc
    inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) =
        inner ℝ ((G₀ f : Ω₀) : H₀) (f : H₀) := real_inner_comm _ _
    _ = B₀ f f := rfl
    _ = GE₀ f ^ 2 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
        f).symm

/-- The Poisson-image--state pairing is exactly the squared Poisson energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_poisson_eq_poissonEnergyNorm_sq
    (u : Ω₀) :
    inner ℝ (A₀ u) u = PE₀ u ^ 2 := by
  change inner ℝ ((A₀ u : Ω₀) : H₀) (u : H₀) = PE₀ u ^ 2
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
      u).symm

/-- Negating the state leaves the positive Green ray point unchanged. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPositiveCauchySchwarzRayPointL2_neg_right
    (f u : Ω₀) :
    GR₀ f (-u) = GR₀ f u := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPositiveCauchySchwarzRayPointL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_neg]

/-- Negating the datum leaves the positive Poisson ray point unchanged. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonPositiveCauchySchwarzRayPointL2_neg_left
    (f u : Ω₀) :
    PR₀ (-f) u = PR₀ f u := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonPositiveCauchySchwarzRayPointL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_neg]

/-- Positive equality in the exact energy Cauchy--Schwarz inequality is
characterized by the positive centered Green ray. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    inner ℝ f u = GE₀ f * PE₀ u ↔
      u = GR₀ f u := by
  have hGreenPos :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_of_ne_zero
      f hf
  have hPoissonPos :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_of_ne_zero
      u hu
  have hGreenNe : GE₀ f ≠ 0 := ne_of_gt hGreenPos
  have hPoissonNe : PE₀ u ≠ 0 := ne_of_gt hPoissonPos
  constructor
  · intro hPair
    let uOne : Ω₀ := (PE₀ u)⁻¹ • u
    have hUOneEnergy : PE₀ uOne = 1 := by
      dsimp [uOne]
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_smul,
        abs_of_pos (inv_pos.mpr hPoissonPos)]
      exact inv_mul_cancel₀ hPoissonNe
    have hUOnePair : inner ℝ f uOne = GE₀ f := by
      have hPairAmbient : inner ℝ (f : H₀) (u : H₀) = GE₀ f * PE₀ u := hPair
      dsimp [uOne]
      change inner ℝ (f : H₀) ((PE₀ u)⁻¹ • (u : H₀)) = GE₀ f
      rw [real_inner_smul_right, hPairAmbient]
      field_simp [hPoissonNe]
    have hUOneEq : uOne = GW₀ f :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
        f uOne hf).1 ⟨le_of_eq hUOneEnergy, hUOnePair⟩
    dsimp [uOne] at hUOneEq
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
      at hUOneEq
    have hUnscaled :
        u = PE₀ u • ((GE₀ f)⁻¹ • G₀ f) :=
      (inv_smul_eq_iff_eq_smul_of_ne
        (PE₀ u) hPoissonNe u ((GE₀ f)⁻¹ • G₀ f)).1 hUOneEq
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPositiveCauchySchwarzRayPointL2
    simpa [smul_smul] using hUnscaled
  · intro hRay
    calc
      inner ℝ f u = inner ℝ f (GR₀ f u) :=
        congrArg (fun z : Ω₀ => inner ℝ f z) hRay
      _ = GE₀ f * PE₀ u := by
        unfold
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPositiveCauchySchwarzRayPointL2
        change
          inner ℝ (f : H₀)
              ((PE₀ u * (GE₀ f)⁻¹) • ((G₀ f : Ω₀) : H₀)) =
            GE₀ f * PE₀ u
        rw [real_inner_smul_right]
        have hInnerSquare :
            inner ℝ (f : H₀) ((G₀ f : Ω₀) : H₀) = GE₀ f ^ 2 := by
          exact
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_centeredGreen_eq_greenEnergyNorm_sq
              f
        rw [hInnerSquare]
        field_simp [hGreenNe]

/-- Positive equality in the exact energy Cauchy--Schwarz inequality is
characterized dually by the positive Poisson ray. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    inner ℝ f u = GE₀ f * PE₀ u ↔
      f = PR₀ f u := by
  have hGreenPos :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_pos_of_ne_zero
      f hf
  have hPoissonPos :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_pos_of_ne_zero
      u hu
  have hGreenNe : GE₀ f ≠ 0 := ne_of_gt hGreenPos
  have hPoissonNe : PE₀ u ≠ 0 := ne_of_gt hPoissonPos
  constructor
  · intro hPair
    let fOne : Ω₀ := (GE₀ f)⁻¹ • f
    have hFOneEnergy : GE₀ fOne = 1 := by
      dsimp [fOne]
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_smul,
        abs_of_pos (inv_pos.mpr hGreenPos)]
      exact inv_mul_cancel₀ hGreenNe
    have hFOnePair : inner ℝ fOne u = PE₀ u := by
      have hPairAmbient : inner ℝ (f : H₀) (u : H₀) = GE₀ f * PE₀ u := hPair
      dsimp [fOne]
      change inner ℝ ((GE₀ f)⁻¹ • (f : H₀)) (u : H₀) = PE₀ u
      rw [real_inner_smul_left, hPairAmbient]
      field_simp [hGreenNe]
    have hFOneEq : fOne = PW₀ u :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
        fOne u hu).1 ⟨le_of_eq hFOneEnergy, hFOnePair⟩
    dsimp [fOne] at hFOneEq
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
      at hFOneEq
    have hUnscaled :
        f = GE₀ f • ((PE₀ u)⁻¹ • A₀ u) :=
      (inv_smul_eq_iff_eq_smul_of_ne
        (GE₀ f) hGreenNe f ((PE₀ u)⁻¹ • A₀ u)).1 hFOneEq
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonPositiveCauchySchwarzRayPointL2
    simpa [smul_smul] using hUnscaled
  · intro hRay
    calc
      inner ℝ f u = inner ℝ (PR₀ f u) u :=
        congrArg (fun z : Ω₀ => inner ℝ z u) hRay
      _ = GE₀ f * PE₀ u := by
        unfold
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonPositiveCauchySchwarzRayPointL2
        change
          inner ℝ
              ((GE₀ f * (PE₀ u)⁻¹) • ((A₀ u : Ω₀) : H₀))
              (u : H₀) =
            GE₀ f * PE₀ u
        rw [real_inner_smul_left]
        have hInnerSquare :
            inner ℝ ((A₀ u : Ω₀) : H₀) (u : H₀) = PE₀ u ^ 2 := by
          exact
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_poisson_eq_poissonEnergyNorm_sq
              u
        rw [hInnerSquare]
        field_simp [hPoissonNe]

/-- Negative equality in the exact energy Cauchy--Schwarz inequality is
characterized by the negative centered Green ray. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_greenPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    inner ℝ f u = -(GE₀ f * PE₀ u) ↔
      u = -(GR₀ f u) := by
  have hNegUNe : -u ≠ 0 := by simpa using hu
  constructor
  · intro hPair
    have hPositiveNeg : inner ℝ f (-u) = GE₀ f * PE₀ (-u) := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_neg]
      have hInnerNeg : inner ℝ f (-u) = -inner ℝ f u := by simp
      rw [hInnerNeg, hPair]
      ring
    have hNegRay : -u = GR₀ f (-u) :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
        f (-u) hf hNegUNe).1 hPositiveNeg
    have hNegRay' : -u = GR₀ f u := by
      calc
        -u = GR₀ f (-u) := hNegRay
        _ = GR₀ f u :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPositiveCauchySchwarzRayPointL2_neg_right
            f u
    have hDoubleNeg := congrArg (fun z : Ω₀ => -z) hNegRay'
    simpa using hDoubleNeg
  · intro hRay
    have hNegRay : -u = GR₀ f u := by
      have hDoubleNeg := congrArg (fun z : Ω₀ => -z) hRay
      simpa using hDoubleNeg
    have hNegRay' : -u = GR₀ f (-u) := by
      calc
        -u = GR₀ f u := hNegRay
        _ = GR₀ f (-u) :=
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPositiveCauchySchwarzRayPointL2_neg_right
            f u).symm
    have hPositiveNeg : inner ℝ f (-u) = GE₀ f * PE₀ (-u) :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
        f (-u) hf hNegUNe).2 hNegRay'
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_neg]
      at hPositiveNeg
    have hInnerNeg : inner ℝ f (-u) = -inner ℝ f u := by simp
    rw [hInnerNeg] at hPositiveNeg
    linarith

/-- Negative equality in the exact energy Cauchy--Schwarz inequality is
characterized dually by the negative Poisson ray. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_poissonPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    inner ℝ f u = -(GE₀ f * PE₀ u) ↔
      f = -(PR₀ f u) := by
  have hNegFNe : -f ≠ 0 := by simpa using hf
  constructor
  · intro hPair
    have hPositiveNeg : inner ℝ (-f) u = GE₀ (-f) * PE₀ u := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_neg]
      have hInnerNeg : inner ℝ (-f) u = -inner ℝ f u := by simp
      rw [hInnerNeg, hPair]
      ring
    have hNegRay : -f = PR₀ (-f) u :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
        (-f) u hNegFNe hu).1 hPositiveNeg
    have hNegRay' : -f = PR₀ f u := by
      calc
        -f = PR₀ (-f) u := hNegRay
        _ = PR₀ f u :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonPositiveCauchySchwarzRayPointL2_neg_left
            f u
    have hDoubleNeg := congrArg (fun z : Ω₀ => -z) hNegRay'
    simpa using hDoubleNeg
  · intro hRay
    have hNegRay : -f = PR₀ f u := by
      have hDoubleNeg := congrArg (fun z : Ω₀ => -z) hRay
      simpa using hDoubleNeg
    have hNegRay' : -f = PR₀ (-f) u := by
      calc
        -f = PR₀ f u := hNegRay
        _ = PR₀ (-f) u :=
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonPositiveCauchySchwarzRayPointL2_neg_left
            f u).symm
    have hPositiveNeg : inner ℝ (-f) u = GE₀ (-f) * PE₀ u :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
        (-f) u hNegFNe hu).2 hNegRay'
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_neg]
      at hPositiveNeg
    have hInnerNeg : inner ℝ (-f) u = -inner ℝ f u := by simp
    rw [hInnerNeg] at hPositiveNeg
    linarith

/-- Absolute equality in the exact energy Cauchy--Schwarz inequality occurs
exactly on the two signed centered Green rays. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_signed_greenPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    |inner ℝ f u| = GE₀ f * PE₀ u ↔
      u = GR₀ f u ∨ u = -(GR₀ f u) := by
  have hProductNonneg : 0 ≤ GE₀ f * PE₀ u :=
    mul_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        u)
  constructor
  · intro hAbs
    rcases
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).1 hAbs with
      hPositive | hNegative
    · left
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
          f u hf hu).1 hPositive
    · right
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_greenPositiveCauchySchwarzRayPointL2
          f u hf hu).1 hNegative
  · rintro (hPositive | hNegative)
    · apply
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).2
      left
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
          f u hf hu).2 hPositive
    · apply
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).2
      right
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_greenPositiveCauchySchwarzRayPointL2
          f u hf hu).2 hNegative

/-- Absolute equality in the exact energy Cauchy--Schwarz inequality occurs
dually exactly on the two signed Poisson rays. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_signed_poissonPositiveCauchySchwarzRayPointL2
    (f u : Ω₀)
    (hf : f ≠ 0)
    (hu : u ≠ 0) :
    |inner ℝ f u| = GE₀ f * PE₀ u ↔
      f = PR₀ f u ∨ f = -(PR₀ f u) := by
  have hProductNonneg : 0 ≤ GE₀ f * PE₀ u :=
    mul_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_nonneg
        f)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
        u)
  constructor
  · intro hAbs
    rcases
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).1 hAbs with
      hPositive | hNegative
    · left
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
          f u hf hu).1 hPositive
    · right
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_poissonPositiveCauchySchwarzRayPointL2
          f u hf hu).1 hNegative
  · rintro (hPositive | hNegative)
    · apply
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).2
      left
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
          f u hf hu).2 hPositive
    · apply
        (abs_eq_iff_eq_or_eq_neg_of_nonneg
          (inner ℝ f u) (GE₀ f * PE₀ u) hProductNonneg).2
      right
      exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_poissonPositiveCauchySchwarzRayPointL2
          f u hf hu).2 hNegative

/-- Structured receipt for all signed equality cases in the actual beta-zero
Green--Poisson energy Cauchy--Schwarz inequality. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyCauchySchwarzEqualityL2Receipt :
    Prop where
  positive_green_ray :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      inner ℝ f u = GE₀ f * PE₀ u ↔ u = GR₀ f u
  negative_green_ray :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      inner ℝ f u = -(GE₀ f * PE₀ u) ↔ u = -(GR₀ f u)
  absolute_green_rays :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      |inner ℝ f u| = GE₀ f * PE₀ u ↔
        u = GR₀ f u ∨ u = -(GR₀ f u)
  positive_poisson_ray :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      inner ℝ f u = GE₀ f * PE₀ u ↔ f = PR₀ f u
  negative_poisson_ray :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      inner ℝ f u = -(GE₀ f * PE₀ u) ↔ f = -(PR₀ f u)
  absolute_poisson_rays :
    ∀ (f u : Ω₀) (hf : f ≠ 0) (hu : u ≠ 0),
      |inner ℝ f u| = GE₀ f * PE₀ u ↔
        f = PR₀ f u ∨ f = -(PR₀ f u)
  claim_boundary :
    True

/-- The exact signed energy Cauchy--Schwarz equality receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyCauchySchwarzEqualityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyCauchySchwarzEqualityL2Receipt := by
  refine
    { positive_green_ray := ?_
      negative_green_ray := ?_
      absolute_green_rays := ?_
      positive_poisson_ray := ?_
      negative_poisson_ray := ?_
      absolute_poisson_rays := ?_
      claim_boundary := trivial }
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_greenPositiveCauchySchwarzRayPointL2
        f u hf hu
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_greenPositiveCauchySchwarzRayPointL2
        f u hf hu
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_signed_greenPositiveCauchySchwarzRayPointL2
        f u hf hu
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_poissonPositiveCauchySchwarzRayPointL2
        f u hf hu
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_eq_neg_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_neg_poissonPositiveCauchySchwarzRayPointL2
        f u hf hu
  · intro f u hf hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_inner_eq_greenEnergyNorm_mul_poissonEnergyNorm_iff_eq_signed_poissonPositiveCauchySchwarzRayPointL2
        f u hf hu

end
end MathlibAnalytic
end MGAP4D
