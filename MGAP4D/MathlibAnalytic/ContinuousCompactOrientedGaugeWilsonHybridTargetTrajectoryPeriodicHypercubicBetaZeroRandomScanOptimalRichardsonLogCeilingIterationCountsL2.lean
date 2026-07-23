import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- Closed-form natural iteration count for a geometric envelope `C q^n ≤ epsilon`.
The natural ceiling automatically returns zero when the logarithmic quotient is
nonpositive. -/
noncomputable def realGeometricLogCeilingIterationCount
    (q C epsilon : ℝ) : ℕ :=
  ⌈Real.log (C / epsilon) / (-Real.log q)⌉₊

/-- The logarithmic natural ceiling gives a valid non-strict geometric stopping
count. -/
theorem realGeometricLogCeilingIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 ≤ C)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ realGeometricLogCeilingIterationCount q C epsilon,
      C * q ^ n ≤ epsilon := by
  intro n hn
  rcases hC.eq_or_lt with hCZero | hCPos
  · subst C
    simp only [zero_mul]
    exact hEpsilon.le
  · have hLogQNeg : Real.log q < 0 :=
      Real.log_neg hqPos hqLtOne
    have hDenPos : 0 < -Real.log q := neg_pos.mpr hLogQNeg
    have hCeil :
        Real.log (C / epsilon) / (-Real.log q) ≤
          (realGeometricLogCeilingIterationCount q C epsilon : ℝ) := by
      unfold realGeometricLogCeilingIterationCount
      exact Nat.le_ceil _
    have hCast :
        (realGeometricLogCeilingIterationCount q C epsilon : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hRatio :
        Real.log (C / epsilon) / (-Real.log q) ≤ (n : ℝ) :=
      hCeil.trans hCast
    have hMul :
        Real.log (C / epsilon) ≤ (n : ℝ) * (-Real.log q) :=
      (div_le_iff₀ hDenPos).1 hRatio
    have hLogs :
        Real.log C + (n : ℝ) * Real.log q ≤ Real.log epsilon := by
      rw [Real.log_div hCPos.ne' hEpsilon.ne'] at hMul
      linarith
    apply
      (Real.log_le_log_iff
        (mul_pos hCPos (pow_pos hqPos n))
        hEpsilon).1
    rw [Real.log_mul hCPos.ne' (pow_ne_zero n hqPos.ne'), Real.log_pow]
    exact hLogs

/-- Strict closed-form geometric stopping count. The half-tolerance makes the
result compatible with strict stopping predicates while retaining a literal
logarithm-and-ceiling expression. -/
noncomputable def realGeometricStrictLogCeilingIterationCount
    (q C epsilon : ℝ) : ℕ :=
  realGeometricLogCeilingIterationCount q C (epsilon / 2)

/-- The strict logarithmic count guarantees `C q^n < epsilon`. -/
theorem realGeometricStrictLogCeilingIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 ≤ C)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ realGeometricStrictLogCeilingIterationCount q C epsilon,
      C * q ^ n < epsilon := by
  intro n hn
  have hHalfPos : 0 < epsilon / 2 := by linarith
  have hHalf :=
    realGeometricLogCeilingIterationCount_spec
      q C (epsilon / 2) hqPos hqLtOne hC hHalfPos n hn
  linarith

/-- The strict count is exactly the natural ceiling of the closed logarithmic
quotient with half tolerance. -/
theorem realGeometricStrictLogCeilingIterationCount_eq_natCeil
    (q C epsilon : ℝ) :
    realGeometricStrictLogCeilingIterationCount q C epsilon =
      ⌈Real.log (C / (epsilon / 2)) / (-Real.log q)⌉₊ := by
  rfl

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "H₀" =>
  Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "Nvec₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
local notation "Res₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
local notation "GE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
local notation "PE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
local notation "Φ₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2
local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2

/-- Explicit strict log-ceiling count for the operator remainder. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ 324 epsilon

/-- Literal `323/325` closed form for the operator-remainder count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount_eq
    (epsilon : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount epsilon =
      ⌈Real.log ((324 : ℝ) / (epsilon / 2)) /
          (-Real.log ((323 : ℝ) / 325))⌉₊ := by
  rfl

/-- The operator remainder is strictly below tolerance from its closed-form
count onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount epsilon,
      ‖Rem₀ n‖ < epsilon := by
  intro n hn
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq]
  exact
    realGeometricStrictLogCeilingIterationCount_spec
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon n hn

/-- The least permanent remainder index is bounded by the closed-form count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_le_logCeilingIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
    epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount_spec
        epsilon hEpsilon)

/-- Explicit strict log-ceiling count for the inverse defect. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ 1 epsilon

/-- The inverse defect is strictly below tolerance from its closed-form count
onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount epsilon,
      ‖Def₀ n‖ < epsilon := by
  intro n hn
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq]
  simpa only [one_mul] using
    (realGeometricStrictLogCeilingIterationCount_spec
      q₀ 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon n hn)

/-- The least permanent inverse-defect index is bounded by the closed-form
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_logCeilingIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
    epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount_spec
        epsilon hEpsilon)

/-- Explicit strict log-ceiling count for pointwise ambient solution error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ (324 * ‖g‖) epsilon

/-- The pointwise ambient solution error is strictly below tolerance from its
closed-form count onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount
          g epsilon,
      ‖Nvec₀ n g - G₀ g‖ < epsilon := by
  intro n hn
  have hEnvelope :=
    realGeometricStrictLogCeilingIterationCount_spec
      q₀ (324 * ‖g‖) epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (mul_nonneg (by norm_num) (norm_nonneg g)) hEpsilon n hn
  have hBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
      n g
  calc
    ‖Nvec₀ n g - G₀ g‖ = ‖G₀ g - Nvec₀ n g‖ := norm_sub_rev _ _
    _ ≤ 324 * q₀ ^ n * ‖g‖ := hBound
    _ = (324 * ‖g‖) * q₀ ^ n := by ring
    _ < epsilon := hEnvelope

/-- The least permanent pointwise-error index is bounded by the closed-form
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount_spec
        g epsilon hEpsilon)

/-- Explicit strict log-ceiling count for the bundled residual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ ‖g‖ epsilon

/-- The bundled residual norm is strictly below tolerance from its closed-form
count onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount
          g epsilon,
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon := by
  intro n hn
  have hEnvelope :=
    realGeometricStrictLogCeilingIterationCount_spec
      q₀ ‖g‖ epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (norm_nonneg g) hEpsilon n hn
  have hBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
      n g
  exact lt_of_le_of_lt hBound (by simpa only [mul_comm] using hEnvelope)

/-- The least permanent residual index is bounded by the closed-form count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount_spec
        g epsilon hEpsilon)

/-- Explicit strict log-ceiling count for the Poisson-energy error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ (324 * ‖g‖) epsilon

/-- The Poisson-energy error is strictly below tolerance from its closed-form
count onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount
          g epsilon,
      PE₀ (Nvec₀ n g - G₀ g) < epsilon := by
  intro n hn
  have hEnergyBound :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
      (Nvec₀ n g - G₀ g)).2
  have hAmbient :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount_spec
      g epsilon hEpsilon n hn
  exact lt_of_le_of_lt hEnergyBound hAmbient

/-- The least permanent Poisson-energy index is bounded by the closed-form
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount_spec
        g epsilon hEpsilon)

/-- Geometric envelope constant for the exact Poisson Fenchel gap. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant
    (g : Ω₀) : ℝ :=
  ((1 : ℝ) / 2) * (324 * ‖g‖) ^ 2

/-- Explicit strict log-ceiling count for the exact Poisson Fenchel gap. The
base is `q_*^2` because the gap is a squared energy error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount
    (q₀ ^ 2)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant g)
    epsilon

/-- Exact geometric envelope for the Poisson Fenchel gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_le_geometricEnvelope
    (g : Ω₀)
    (n : ℕ) :
    ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant g *
        (q₀ ^ 2) ^ n := by
  have hEnergyAmbient :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
      (Nvec₀ n g - G₀ g)).2
  have hAmbient :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
      n g
  have hAmbient' :
      ‖Nvec₀ n g - G₀ g‖ ≤ 324 * q₀ ^ n * ‖g‖ := by
    simpa only [norm_sub_rev] using hAmbient
  have hEnergy :
      PE₀ (Nvec₀ n g - G₀ g) ≤ 324 * q₀ ^ n * ‖g‖ :=
    hEnergyAmbient.trans hAmbient'
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      (Nvec₀ n g - G₀ g)
  have hRightNonneg : 0 ≤ 324 * q₀ ^ n * ‖g‖ :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg
          (le_of_lt
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
          n))
      (norm_nonneg g)
  have hSq :
      PE₀ (Nvec₀ n g - G₀ g) ^ 2 ≤
        (324 * q₀ ^ n * ‖g‖) ^ 2 := by
    nlinarith
  have hPowSq : (q₀ ^ n) ^ 2 = (q₀ ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq]
  calc
    ((1 : ℝ) / 2) * PE₀ (Nvec₀ n g - G₀ g) ^ 2 ≤
        ((1 : ℝ) / 2) * (324 * q₀ ^ n * ‖g‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hSq (by norm_num)
    _ = ((1 : ℝ) / 2) * (324 * ‖g‖) ^ 2 * (q₀ ^ n) ^ 2 := by
      ring
    _ =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant g *
          (q₀ ^ 2) ^ n := by
      rw [hPowSq]
      unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant
      rfl

/-- The exact Poisson Fenchel gap is strictly below tolerance from its
closed-form count onwards. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount
          g epsilon,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  intro n hn
  have hEnvelope :=
    realGeometricStrictLogCeilingIterationCount_spec
      (q₀ ^ 2)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGapEnvelopeConstant g)
      epsilon
      (by
        norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2])
      (by
        norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2])
      (mul_nonneg (by norm_num) (sq_nonneg _))
      hEpsilon n hn
  exact lt_of_le_of_lt
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_le_geometricEnvelope
      g n)
    hEnvelope

/-- The least permanent Fenchel-gap index is bounded by the closed-form count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount_spec
        g epsilon hEpsilon)

/-- Explicit strict log-ceiling count for the operational residual-only
certificate. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictLogCeilingIterationCount q₀ (324 * ‖g‖) epsilon

/-- From the residual-only closed-form count onwards, the residual threshold and
a posteriori ambient error certificate both hold. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount
          g epsilon,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        ‖G₀ g - Nvec₀ n g‖ ≤ epsilon := by
  intro n hn
  have hEnvelope :=
    realGeometricStrictLogCeilingIterationCount_spec
      q₀ (324 * ‖g‖) epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (mul_nonneg (by norm_num) (norm_nonneg g)) hEpsilon n hn
  have hResidualBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
      n g
  have hScaledResidual :
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ ≤
        (324 * ‖g‖) * q₀ ^ n := by
    calc
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ ≤
          324 * (q₀ ^ n * ‖g‖) :=
        mul_le_mul_of_nonneg_left hResidualBound (by norm_num)
      _ = (324 * ‖g‖) * q₀ ^ n := by ring
  have hResidualSmall := lt_of_le_of_lt hScaledResidual hEnvelope
  refine ⟨hResidualSmall, ?_⟩
  have hErrorBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
      n g
  have hEnvelopeLe : (324 * ‖g‖) * q₀ ^ n ≤ epsilon :=
    le_of_lt hEnvelope
  calc
    ‖G₀ g - Nvec₀ n g‖ ≤ 324 * q₀ ^ n * ‖g‖ := hErrorBound
    _ = (324 * ‖g‖) * q₀ ^ n := by ring
    _ ≤ epsilon := hEnvelopeLe

/-- The least residual-certified index is bounded by the residual-only
closed-form count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (fun n hn =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount_spec
          g epsilon hEpsilon n hn).1)

/-- A single explicit count satisfying all six strict stopping conditions. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  max
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount epsilon)
    (max
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount epsilon)
      (max
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount g epsilon)
        (max
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount g epsilon)
          (max
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount g epsilon)
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount g epsilon)))))

/-- All six stopping conditions hold from the explicit simultaneous count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount
          g epsilon,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  intro n hn
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount at hn
  refine
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount_spec
        epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount_spec
        epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount_spec
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount_spec
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount_spec
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount_spec
        g epsilon hEpsilon n (by omega)⟩

/-- The least simultaneous permanent index is bounded by the explicit
simultaneous count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_le_logCeilingIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount_spec
        g epsilon hEpsilon)

/-- Structured receipt for the generic and actual closed-form Richardson
iteration counts. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogCeilingIterationCountsL2Receipt :
    Prop where
  generic_nonstrict :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 ≤ C → 0 < epsilon →
      ∀ n ≥ realGeometricLogCeilingIterationCount q C epsilon,
        C * q ^ n ≤ epsilon
  generic_strict :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 ≤ C → 0 < epsilon →
      ∀ n ≥ realGeometricStrictLogCeilingIterationCount q C epsilon,
        C * q ^ n < epsilon
  operator_remainder_count :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount epsilon,
        ‖Rem₀ n‖ < epsilon
  inverse_defect_count :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount epsilon,
        ‖Def₀ n‖ < epsilon
  pointwise_error_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount g epsilon,
        ‖Nvec₀ n g - G₀ g‖ < epsilon
  residual_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount g epsilon,
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon
  poisson_energy_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount g epsilon,
        PE₀ (Nvec₀ n g - G₀ g) < epsilon
  fenchel_gap_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount g epsilon,
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  residual_certificate_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount g epsilon,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          ‖G₀ g - Nvec₀ n g‖ ≤ epsilon
  simultaneous_count :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount g epsilon,
        ‖Rem₀ n‖ < epsilon ∧
        ‖Def₀ n‖ < epsilon ∧
        ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  claim_boundary : True

/-- The closed-form iteration-count receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogCeilingIterationCountsL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogCeilingIterationCountsL2Receipt := by
  exact
    { generic_nonstrict := realGeometricLogCeilingIterationCount_spec
      generic_strict := realGeometricStrictLogCeilingIterationCount_spec
      operator_remainder_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logCeilingIterationCount_spec
      inverse_defect_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logCeilingIterationCount_spec
      pointwise_error_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logCeilingIterationCount_spec
      residual_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logCeilingIterationCount_spec
      poisson_energy_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logCeilingIterationCount_spec
      fenchel_gap_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logCeilingIterationCount_spec
      residual_certificate_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logCeilingIterationCount_spec
      simultaneous_count :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogCeilingIterationCount_spec
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
