import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSpectralEndpointsL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous-linear-map eigenvector remains an eigenvector of every power,
with the eigenvalue raised to the same power. -/
theorem continuousLinearMap_pow_apply_of_apply_eq_smul
    (T : V →L[ℝ] V)
    (f : V)
    (rho : ℝ)
    (hEigen : T f = rho • f)
    (n : ℕ) :
    (T ^ n) f = rho ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (T ^ (n + 1)) f = T ((T ^ n) f) := by
          simp [pow_succ']
        _ = T (rho ^ n • f) := by rw [ih]
        _ = rho ^ n • T f := by simp
        _ = rho ^ n • (rho • f) := by rw [hEigen]
        _ = rho ^ (n + 1) • f := by
          simp [pow_succ, smul_smul]

/-- Raising nonnegative real numbers to a common natural power preserves order. -/
theorem real_pow_le_pow_of_nonneg
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (n : ℕ) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) n)

/-- The exact nonstationary spectral decay factor after `n` random-scan steps. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2
    (n : ℕ) : ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 ^ n

/-- A scalar is the exact `n`-step nonstationary spectral decay factor when it
bounds every powered nonstationary spectral modulus and is attained. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactNStepSLEML2
    (n : ℕ)
    (r : ℝ) : Prop :=
  (∀ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
      rho ≠ 1 →
      |rho| ^ n ≤ r) ∧
    ∃ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
      rho ≠ 1 ∧
      |rho| ^ n = r

/-- The exact `n`-step SLEM factor is nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg
    (n : ℕ) :
    0 ≤ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  exact pow_nonneg (by
    norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]) n

/-- Every nonstationary full-spectrum value decays at most at the exact `n`-step
SLEM factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_pow_le_nStepSLEM_of_ne_one
    (n : ℕ)
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2)
    (hNe : rho ≠ 1) :
    |rho| ^ n ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  have hOneStep :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_le_slem_of_ne_one
      rho hRho hNe
  exact real_pow_le_pow_of_nonneg (abs_nonneg rho) hOneStep n

/-- The second spectral value attains the exact `n`-step SLEM factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_pow_eq_nStepSLEM
    (n : ℕ) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2| ^ n =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_eq_slem]
  rfl

/-- The exact nonstationary spectral decay factor after `n` steps is
`(323 / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_isExact
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactNStepSLEML2
      n
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n) := by
  constructor
  · intro rho hRho hNe
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_pow_le_nStepSLEM_of_ne_one
        n rho hRho hNe
  · exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_pow_eq_nStepSLEM n⟩

/-- The exact `n`-step characterization determines the decay factor uniquely. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanIsExactNStepSLEML2_unique
    (n : ℕ)
    {r : ℝ}
    (hR :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactNStepSLEML2
        n r) :
    r = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  rcases hR.2 with ⟨rho, hRho, hNe, hAttain⟩
  have hUpper :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_pow_le_nStepSLEM_of_ne_one
      n rho hRho hNe
  rw [hAttain] at hUpper
  have hLower := hR.1
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_pow_eq_nStepSLEM]
    at hLower
  exact le_antisymm hUpper hLower

/-- On the cardinality-`k` eigenspace, the `n`-step random-scan operator acts by
exactly `(1 - k / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
    (k n : ℕ)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f =
      (1 - (k : ℝ) / 324) ^ n • f := by
  apply continuousLinearMap_pow_apply_of_apply_eq_smul
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2,
    Module.End.mem_genEigenspace_one] at hf
  exact hf

/-- Every nonstationary cardinality eigenspace contracts in norm no slower than
`(323 / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_mem_cardinalityEigenspace
    (k n : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k) :
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n * ‖f‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
    k n f hf, norm_smul, Real.norm_eq_abs, abs_pow]
  let kFin : Fin 325 := ⟨k, by omega⟩
  have hAbs :
      |1 - (k : ℝ) / 324| ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
    simpa [kFin, periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2] using
      fin_affine_grid_abs_le_second_of_ne_zero 324 (by omega) kFin (by omega)
  have hPow := real_pow_le_pow_of_nonneg (abs_nonneg (1 - (k : ℝ) / 324)) hAbs n
  exact mul_le_mul_of_nonneg_right hPow (norm_nonneg f)

/-- The second eigenspace realizes the exact geometric norm-decay factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_eq_nStepSLEM_mul_norm_of_mem_secondEigenspace
    (n : ℕ)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2) :
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n * ‖f‖ := by
  have hfCard : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 1 := by
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinality_one]
    exact hf
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
    1 n f hfCard, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · rfl
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg n

/-- The stationary cardinality-zero sector is fixed by every random-scan power. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_self_of_mem_stationaryEigenspace
    (n : ℕ)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 0) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f = f := by
  have h :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
      0 n f hf
  simpa using h

/-- The zero eigenspace is annihilated by every positive random-scan power. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_zero_of_mem_zeroEigenspace
    (n : ℕ)
    (hn : 0 < n)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f = 0 := by
  have hfCard : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 324 := by
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324]
    exact hf
  have h :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
      324 n f hfCard
  simpa [zero_pow hn] using h

/-- Compact receipt for exact finite-volume beta-zero random-scan `n`-step
spectral decay and endpoint-sector dynamics. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSpectralDecayL2Receipt :
    Prop :=
  (∀ n : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactNStepSLEML2
      n
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n)) ∧
  (∀ k n : ℕ,
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k →
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f =
        (1 - (k : ℝ) / 324) ^ n • f) ∧
  (∀ n : ℕ,
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 →
      ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n * ‖f‖) ∧
  (∀ n : ℕ,
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 0 →
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f = f) ∧
  (∀ n : ℕ, 0 < n →
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 →
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f = 0)

/-- The exact beta-zero random-scan `n`-step spectral-decay receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSpectralDecayL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSpectralDecayL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_isExact,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_eq_nStepSLEM_mul_norm_of_mem_secondEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_self_of_mem_stationaryEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_zero_of_mem_zeroEigenspace⟩

end

end MathlibAnalytic
end MGAP4D