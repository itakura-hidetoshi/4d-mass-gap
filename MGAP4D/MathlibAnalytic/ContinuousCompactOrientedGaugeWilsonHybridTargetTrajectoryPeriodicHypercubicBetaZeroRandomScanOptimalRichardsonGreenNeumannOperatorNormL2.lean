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

local notation "E₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "A₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "τ₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "R₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2 τ₀

/-- The continuous-linear iterate of the optimal Richardson error endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2 :
    ℕ → E₀ →L[ℝ] E₀
  | 0 => ContinuousLinearMap.id ℝ E₀
  | Nat.succ n =>
      R₀.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2
          n)

local notation "Rpow₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2

/-- The continuous-linear iterate acts as the previously defined pointwise error
iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply
    (n : ℕ) (e : E₀) :
    Rpow₀ n e =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      change R₀ (Rpow₀ n e) =
        R₀
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
            n e)
      rw [ih]

/-- Repeated application preserves an attained scalar endpoint and raises its
multiplier to the corresponding power. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul_of_apply_eq_factor_smul
    (n : ℕ) (e : E₀) (hEndpoint : R₀ e = q₀ • e) :
    Rpow₀ n e = q₀ ^ n • e := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorEndIterateL2]
      change R₀ (Rpow₀ n e) = q₀ ^ Nat.succ n • e
      rw [ih, map_smul, hEndpoint, smul_smul, pow_succ]

/-- Operator-norm upper bound for every finite optimal Richardson error iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_le
    (n : ℕ) :
    ‖Rpow₀ n‖ ≤ q₀ ^ n := by
  apply (Rpow₀ n).opNorm_le_bound
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
    ∃ e : E₀, e ≠ 0 ∧ Rpow₀ n e = q₀ ^ n • e := by
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
    ‖Rpow₀ n‖ = q₀ ^ n := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_le
        n
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndIterateL2_apply_eq_pow_factor_smul
        n
      with ⟨e, heNe, hAction⟩
    have hFundamental := (Rpow₀ n).le_opNorm e
    have hPowNonneg : 0 ≤ q₀ ^ n :=
      pow_nonneg
        (le_of_lt
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
        n
    rw [hAction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hPowNonneg]
      at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [ContinuousLinearMap.opNorm_nonneg (Rpow₀ n)]

/-- The finite Green-Neumann approximation, bundled as a continuous linear
endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
    (n : ℕ) : E₀ →L[ℝ] E₀ :=
  G₀ - (Rpow₀ n).comp G₀

local notation "N₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2

/-- The bundled continuous-linear finite approximation agrees pointwise with the
zero-start Green-Neumann solver iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply
    (n : ℕ) (g : E₀) :
    N₀ n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g := by
  change
    G₀ g - Rpow₀ n (G₀ g) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndIterateL2_apply,
    ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_eq_errorIterate]
  module

/-- The Green-Neumann truncation remainder as a continuous linear endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
    (n : ℕ) : E₀ →L[ℝ] E₀ :=
  G₀ - N₀ n

local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2

/-- Exact continuous-linear remainder representation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_eq_errorEndIterate_comp_centeredGreen
    (n : ℕ) :
    Rem₀ n = (Rpow₀ n).comp G₀ := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannEndL2
  apply ContinuousLinearMap.ext
  intro g
  change G₀ g - (G₀ g - Rpow₀ n (G₀ g)) = Rpow₀ n (G₀ g)
  module

/-- Pointwise action of the continuous-linear Green-Neumann remainder. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_apply
    (n : ℕ) (g : E₀) :
    Rem₀ n g = Rpow₀ n (G₀ g) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_eq_errorEndIterate_comp_centeredGreen]
  rfl

/-- Operator-norm upper bound for the Green-Neumann truncation remainder. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_le
    (n : ℕ) :
    ‖Rem₀ n‖ ≤ 324 * q₀ ^ n := by
  apply (Rem₀ n).opNorm_le_bound
  · exact
      mul_nonneg (by norm_num)
        (pow_nonneg
          (le_of_lt
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
          n)
  · intro g
    change ‖G₀ g - N₀ n g‖ ≤ (324 * q₀ ^ n) * ‖g‖
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_apply]
    simpa only [mul_assoc] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
        n g

/-- The cardinality-one Poisson endpoint simultaneously gives Green eigenvalue
`324` and positive Richardson eigenvalue `q_*`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_centeredGreen_apply_eq_324_smul_and_optimalRichardsonErrorEnd_apply_eq_factor_smul :
    ∃ e : E₀, e ≠ 0 ∧ G₀ e = (324 : ℝ) • e ∧ R₀ e = q₀ • e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨e, heNe, hPoisson⟩
  have hGreen : G₀ e = (324 : ℝ) • e := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_injective
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self,
      map_smul,
      hPoisson,
      smul_smul]
    norm_num
  have hRichardson : R₀ e = q₀ • e := by
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
    ‖Rem₀ n‖ = 324 * q₀ ^ n := by
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
    have hAction : Rem₀ n e = (324 * q₀ ^ n) • e := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_apply,
        hGreen,
        map_smul,
        hIterate,
        smul_smul]
    have hFundamental := (Rem₀ n).le_opNorm e
    have hCoeffNonneg : 0 ≤ 324 * q₀ ^ n :=
      mul_nonneg (by norm_num)
        (pow_nonneg
          (le_of_lt
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
          n)
    rw [hAction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hCoeffNonneg]
      at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [ContinuousLinearMap.opNorm_nonneg (Rem₀ n)]

/-- The Green-Neumann remainder tends to zero in operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_tendsto_zero :
    Tendsto (fun n : ℕ => ‖Rem₀ n‖) atTop (nhds 0) := by
  have hPow : Tendsto (fun n : ℕ => q₀ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
  have hEnvelope :
      Tendsto (fun n : ℕ => 324 * q₀ ^ n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hPow)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq] using
    hEnvelope

/-- Equivalently, the finite Green-Neumann maps converge to the exact centered
Green inverse in operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannEndL2_tendsto_centeredGreen_in_operatorNorm :
    Tendsto (fun n : ℕ => ‖G₀ - N₀ n‖) atTop (nhds 0) := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_tendsto_zero

/-- The inverse defect `I - A N_n` of the finite Green-Neumann approximation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
    (n : ℕ) : E₀ →L[ℝ] E₀ :=
  ContinuousLinearMap.id ℝ E₀ - A₀.comp (N₀ n)

local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- Pointwise, the inverse defect is exactly the `n`th Richardson error iterate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_apply
    (n : ℕ) (g : E₀) :
    Def₀ n g = Rpow₀ n g := by
  change g - A₀ (N₀ n g) = Rpow₀ n g
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
    Def₀ n = Rpow₀ n := by
  apply ContinuousLinearMap.ext
  intro g
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_apply
      n g

/-- Exact operator norm of the finite Green-Neumann inverse defect. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq
    (n : ℕ) :
    ‖Def₀ n‖ = q₀ ^ n := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_eq_errorEndIterate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndIterateL2_eq]

/-- The finite Green-Neumann inverse defects converge to zero in operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_tendsto_zero_in_operatorNorm :
    Tendsto (fun n : ℕ => ‖Def₀ n‖) atTop (nhds 0) := by
  have hPow : Tendsto (fun n : ℕ => q₀ ^ n) atTop (nhds 0) :=
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
  continuous_apply : ∀ (n : ℕ) (g : E₀),
    N₀ n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g
  exact_error_iterate_norm : ∀ n : ℕ, ‖Rpow₀ n‖ = q₀ ^ n
  exact_green_remainder_norm : ∀ n : ℕ, ‖Rem₀ n‖ = 324 * q₀ ^ n
  green_operator_norm_limit :
    Tendsto (fun n : ℕ => ‖G₀ - N₀ n‖) atTop (nhds 0)
  exact_inverse_defect : ∀ n : ℕ, Def₀ n = Rpow₀ n
  exact_inverse_defect_norm : ∀ n : ℕ, ‖Def₀ n‖ = q₀ ^ n
  inverse_defect_operator_norm_limit :
    Tendsto (fun n : ℕ => ‖Def₀ n‖) atTop (nhds 0)

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
