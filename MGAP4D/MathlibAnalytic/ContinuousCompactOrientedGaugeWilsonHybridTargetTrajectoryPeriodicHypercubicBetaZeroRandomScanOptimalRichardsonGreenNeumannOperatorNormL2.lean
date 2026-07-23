import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonGreenNeumannL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- The continuous-linear iterate of the optimal Richardson error endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2 :
    ℕ →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
  | 0 =>
      ContinuousLinearMap.id ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
  | Nat.succ n =>
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2).comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n)

/-- The continuous-linear iterate acts as the previously defined pointwise error
iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply
    (n : ℕ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n e =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n e := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      change
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
              n e) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n e)
      rw [ih]

/-- Repeated application preserves an attained scalar endpoint and raises its
multiplier to the corresponding power. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul_of_apply_eq_factor_smul
    (n : ℕ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hEndpoint :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n e =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n •
        e := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2]
      change
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
              n e) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^
              Nat.succ n •
            e
      rw [ih, map_smul, hEndpoint, smul_smul, pow_succ]

/-- Operator-norm upper bound for every finite optimal Richardson error iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_le
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
      n).opNorm_le_bound
  · exact
      pow_nonneg
        (le_of_lt
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
        n
  · intro e
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
        n e

/-- A cardinality-one endpoint attains the `n`th power of the optimal Richardson
factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul
    (n : ℕ) :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul
    with ⟨e, heNe, hEndpoint⟩
  exact
    ⟨e, heNe,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul_of_apply_eq_factor_smul
        n e hEndpoint⟩

/-- Exact operator norm of the `n`th optimal Richardson error iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_eq
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_le
        n
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul
        n
      with ⟨e, heNe, hAction⟩
    have hFundamental :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n).le_opNorm e
    have hPowNonneg :
        0 ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n :=
      pow_nonneg
        (le_of_lt
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
        n
    rw [hAction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hPowNonneg]
      at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [
      ContinuousLinearMap.opNorm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n)]

/-- The finite Green-Neumann approximation, bundled as a continuous linear
endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2 -
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
      n).comp
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2

/-- The bundled continuous-linear finite approximation agrees pointwise with the
zero-start Green-Neumann solver iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
        n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g := by
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply,
    ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_eq_errorIterate]
  module

/-- The Green-Neumann truncation remainder as a continuous linear endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2 -
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
      n

/-- Exact continuous-linear remainder representation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_eq_errorEndIterate_comp_centeredGreen
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
        n =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n).comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2 := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
  apply ContinuousLinearMap.ext
  intro g
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
            n
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g)
  module

/-- Pointwise action of the continuous-linear Green-Neumann remainder. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_apply
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
        n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_eq_errorEndIterate_comp_centeredGreen]
  rfl

/-- Operator-norm upper bound for the Green-Neumann truncation remainder. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_le
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
        n‖ ≤
      324 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
      n).opNorm_le_bound
  · exact
      mul_nonneg (by norm_num)
        (pow_nonneg
          (le_of_lt
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
          n)
  · intro g
    change
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
            n g‖ ≤
        (324 *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n) *
          ‖g‖
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply]
    simpa only [mul_assoc] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
        n g

/-- The cardinality-one Poisson endpoint simultaneously gives Green eigenvalue
`324` and positive Richardson eigenvalue `q_*`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_centeredGreen_apply_eq_324_smul_and_optimalRichardsonErrorEnd_apply_eq_factor_smul :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          e =
        (324 : ℝ) • e ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨e, heNe, hPoisson⟩
  have hGreen :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          e =
        (324 : ℝ) • e := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_injective
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self,
      map_smul,
      hPoisson,
      smul_smul]
    norm_num
  have hRichardson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e := by
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply,
      hPoisson]
    unfold
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
    module
  exact ⟨e, heNe, hGreen, hRichardson⟩

/-- The exact Green-Neumann remainder operator norm is `324 q_*^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
        n‖ =
      324 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_le
        n
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_centeredGreen_apply_eq_324_smul_and_optimalRichardsonErrorEnd_apply_eq_factor_smul
      with ⟨e, heNe, hGreen, hRichardson⟩
    have hIterate :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul_of_apply_eq_factor_smul
        n e hRichardson
    have hAction :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
            n e =
          (324 *
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n) •
            e := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_apply,
        hGreen,
        map_smul,
        hIterate,
        smul_smul]
    have hFundamental :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
        n).le_opNorm e
    have hCoeffNonneg :
        0 ≤
          324 *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n :=
      mul_nonneg (by norm_num)
        (pow_nonneg
          (le_of_lt
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
          n)
    rw [hAction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hCoeffNonneg]
      at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [
      ContinuousLinearMap.opNorm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
          n)]

/-- The finite Green-Neumann endomorphisms converge to the exact centered Green
inverse in operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_tendsto_centeredGreen_in_operatorNorm :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
          n)
      atTop
      (nhds
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hPow :
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
  have hEnvelope :
      Tendsto
        (fun n : ℕ =>
          324 *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hPow)
  simpa only [
    norm_sub_rev,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq] using
    hEnvelope

/-- The inverse defect `I - A N_n` of the finite Green-Neumann approximation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  ContinuousLinearMap.id ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 -
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2.comp
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
        n)

/-- Pointwise, the inverse defect is exactly the `n`th Richardson error iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_apply
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
        n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n g := by
  change
    g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
            n g) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply]
  have hResidual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_eq_errorIterate
      n g
  rw [← hResidual]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_subtype_eq_centeredGreen,
    map_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- The inverse-defect endomorphism is exactly the continuous Richardson iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_eq_errorEndIterate
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
        n =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
        n := by
  apply ContinuousLinearMap.ext
  intro g
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_apply
      n g

/-- Exact operator norm of the finite Green-Neumann inverse defect. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_eq_errorEndIterate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_eq]

/-- The finite Green-Neumann inverse defects converge to zero in operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_tendsto_zero_in_operatorNorm :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
          n)
      atTop
      (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hPow :
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq] using
    hPow

/-- Structured receipt for exact operator-norm Green-Neumann approximation and
inverse-defect convergence. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannOperatorNormL2Receipt :
    Prop where
  continuous_apply :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
          n g =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g
  exact_error_iterate_norm :
    ∀ n : ℕ,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n
  exact_green_remainder_norm :
    ∀ n : ℕ,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
          n‖ =
        324 *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n
  green_operator_norm_limit :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
          n)
      atTop
      (nhds
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2)
  exact_inverse_defect :
    ∀ n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
          n =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n
  exact_inverse_defect_norm :
    ∀ n : ℕ,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
          n‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n
  inverse_defect_operator_norm_limit :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
          n)
      atTop
      (nhds 0)

/-- The exact operator-norm Green-Neumann approximation receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannOperatorNormL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannOperatorNormL2Receipt := by
  exact
    { continuous_apply :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply
      exact_error_iterate_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_eq
      exact_green_remainder_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq
      green_operator_norm_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_tendsto_centeredGreen_in_operatorNorm
      exact_inverse_defect :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_eq_errorEndIterate
      exact_inverse_defect_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq
      inverse_defect_operator_norm_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_tendsto_zero_in_operatorNorm }

end

end MathlibAnalytic
end MGAP4D
