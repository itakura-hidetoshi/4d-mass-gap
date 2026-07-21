import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanNStepSpectralDecayL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A nonnegative geometric scalar with ratio strictly below one sends every fixed
vector to zero under scalar multiplication. -/
theorem tendsto_pow_smul_const_atTop_nhds_zero_of_nonneg_lt_one
    {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr1 : r < 1)
    (f : V) :
    Tendsto (fun n : ℕ => r ^ n • f) atTop (𝓝 0) := by
  have hPow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  simpa using hPow.smul_const f

/-- A real geometric sequence tends to zero whenever its modulus is bounded by a
strictly subunit scalar. -/
theorem tendsto_pow_atTop_nhds_zero_of_abs_le_of_lt_one
    {rho r : ℝ}
    (hAbs : |rho| ≤ r)
    (hr1 : r < 1) :
    Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (lt_of_le_of_lt hAbs hr1)

/-- The exact beta-zero random-scan `n`-step SLEM factor converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_tendsto_zero :
    Tendsto
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2
      atTop
      (𝓝 0) := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by
        norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2])
      (by
        norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]))

/-- Every nonstationary full-spectrum scalar has powers converging to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_pow_tendsto_zero_of_ne_one
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2)
    (hNe : rho ≠ 1) :
    Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) := by
  have hAbs :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_le_slem_of_ne_one
      rho hRho hNe
  apply tendsto_pow_atTop_nhds_zero_of_abs_le_of_lt_one hAbs
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- Every vector in a nonstationary cardinality eigenspace converges strongly to
zero under repeated beta-zero random-scan updates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_nonstationary_cardinalityEigenspace
    (k : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324)
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 0) := by
  have hkReal : (k : ℝ) ≤ 324 := by
    exact_mod_cast hUpper
  have hkPosNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hLower
  have hkPos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hkPosNat
  have hDen : (0 : ℝ) < 324 := by norm_num
  have hRatioLe : (k : ℝ) / 324 ≤ 1 :=
    (div_le_one hDen).2 hkReal
  have hRatioPos : 0 < (k : ℝ) / 324 :=
    div_pos hkPos hDen
  have hScalar0 : 0 ≤ 1 - (k : ℝ) / 324 := by
    linarith
  have hScalar1 : 1 - (k : ℝ) / 324 < 1 := by
    linarith
  have hGeometric :=
    tendsto_pow_smul_const_atTop_nhds_zero_of_nonneg_lt_one
      hScalar0 hScalar1 f
  have hFunction :
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f) =
        (fun n : ℕ => (1 - (k : ℝ) / 324) ^ n • f) := by
    funext n
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
        k n f hf
  rw [hFunction]
  exact hGeometric

/-- The second eigenspace realizes strong geometric convergence to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_secondEigenspace
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 0) := by
  have hfCard : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 1 := by
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne]
    exact hf
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_nonstationary_cardinalityEigenspace
      1 (by omega) (by omega) f hfCard

/-- The norm of every second-eigenspace orbit converges to zero at the exact
geometric rate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_tendsto_zero_of_mem_secondEigenspace
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2) :
    Tendsto
      (fun n : ℕ =>
        ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f‖)
      atTop
      (𝓝 0) := by
  have hOrbit :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_secondEigenspace
      f hf
  simpa using hOrbit.norm

/-- The stationary cardinality-zero sector remains fixed at every time and hence
converges to its initial vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_self_of_mem_stationaryEigenspace
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 0) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 f) := by
  have hFunction :
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f) =
        (fun _ : ℕ => f) := by
    funext n
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_self_of_mem_stationaryEigenspace
        n f hf
  rw [hFunction]
  exact tendsto_const_nhds

/-- The zero eigenspace converges strongly to zero; in fact every positive power
already annihilates it. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_zeroEigenspace
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 0) := by
  have hfCard : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 324 := by
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324]
    exact hf
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_nonstationary_cardinalityEigenspace
      324 (by omega) (by omega) f hfCard

/-- Compact receipt for exact finite-volume beta-zero random-scan long-time
spectral convergence. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralConvergenceL2Receipt :
    Prop :=
  Tendsto
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2
      atTop
      (𝓝 0) ∧
  (∀ rho : ℝ,
    rho ∈ spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
    rho ≠ 1 →
    Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0)) ∧
  (∀ k : ℕ, 1 ≤ k → k ≤ 324 →
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k →
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
        atTop
        (𝓝 0)) ∧
  (∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 →
    Tendsto
      (fun n : ℕ =>
        ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f‖)
      atTop
      (𝓝 0)) ∧
  (∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 0 →
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 f)) ∧
  (∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 →
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) f)
      atTop
      (𝓝 0))

/-- The exact beta-zero random-scan spectral-convergence receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralConvergenceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralConvergenceL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_tendsto_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_pow_tendsto_zero_of_ne_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_nonstationary_cardinalityEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_tendsto_zero_of_mem_secondEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_self_of_mem_stationaryEigenspace,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_zero_of_mem_zeroEigenspace⟩

end

end MathlibAnalytic
end MGAP4D
