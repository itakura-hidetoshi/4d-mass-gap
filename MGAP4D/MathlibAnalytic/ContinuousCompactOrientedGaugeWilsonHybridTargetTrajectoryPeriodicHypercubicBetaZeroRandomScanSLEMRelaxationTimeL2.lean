import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanExactSpectralGapL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Every value in the positive finite affine grid `1 - k / N` is nonnegative. -/
theorem fin_affine_grid_nonneg
    (N : ℕ)
    (hN : 0 < N)
    (k : Fin (N + 1)) :
    0 ≤ 1 - (k.1 : ℝ) / N := by
  have hkNat : k.1 ≤ N := by
    omega
  have hkReal : (k.1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hkNat
  have hNReal : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hDiv : (k.1 : ℝ) / (N : ℝ) ≤ 1 := by
    exact (div_le_one hNReal).2 hkReal
  linarith

/-- In a positive finite affine grid, the absolute value of every nonstationary
entry is bounded by the first nonstationary entry `1 - 1 / N`. -/
theorem fin_affine_grid_abs_le_second_of_ne_zero
    (N : ℕ)
    (hN : 0 < N)
    (k : Fin (N + 1))
    (hk : k.1 ≠ 0) :
    |1 - (k.1 : ℝ) / N| ≤ 1 - (1 : ℝ) / N := by
  rw [abs_of_nonneg (fin_affine_grid_nonneg N hN k)]
  have hGap := fin_affine_grid_inv_le_gap_of_ne_zero N hN k hk
  simpa [one_div] using (show
    1 - (k.1 : ℝ) / N ≤ 1 - (1 : ℝ) / N by
      linarith)

/-- The second-largest eigenvalue modulus of the actual finite-volume beta-zero
random-scan operator. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 : ℝ :=
  1 - (1 : ℝ) / 324

/-- The corresponding absolute spectral gap. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2 : ℝ :=
  1 - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2

/-- The finite-volume beta-zero random-scan relaxation time. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRelaxationTimeL2 : ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2⁻¹

/-- A scalar is an exact second-largest eigenvalue modulus when it bounds the
absolute value of every nonstationary full-spectrum value and is attained by
one such value. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSLEML2
    (r : ℝ) : Prop :=
  (∀ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
      rho ≠ 1 →
      |rho| ≤ r) ∧
    ∃ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
      rho ≠ 1 ∧
      |rho| = r

/-- Every full-spectrum value of the actual beta-zero random-scan operator is
nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_nonneg_of_mem
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2) :
    0 ≤ rho := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
    at hRho
  rcases hRho with ⟨k, rfl⟩
  exact fin_affine_grid_nonneg 324 (by omega) k

/-- Every nonstationary full-spectrum value has modulus at most `323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_le_slem_of_ne_one
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2)
    (hNe : rho ≠ 1) :
    |rho| ≤ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
    at hRho
  rcases hRho with ⟨k, rfl⟩
  have hk : k.1 ≠ 0 := by
    intro hkZero
    apply hNe
    simp [hkZero]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2] using
    fin_affine_grid_abs_le_second_of_ne_zero 324 (by omega) k hk

/-- The largest nonstationary spectral value has modulus equal to the SLEM. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_eq_slem :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2| =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- The value `323 / 324` is the exact beta-zero random-scan SLEM. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSLEML2_isExact :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSLEML2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
  constructor
  · intro rho hRho hNe
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_le_slem_of_ne_one
        rho hRho hNe
  · exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_eq_slem⟩

/-- The exact-SLEM characterization determines the SLEM uniquely. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanIsExactSLEML2_unique
    {r : ℝ}
    (hR : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSLEML2 r) :
    r = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
  rcases hR.2 with ⟨rho, hRho, hNe, hAttain⟩
  have hUpper :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSpectrumL2_le_slem_of_ne_one
      rho hRho hNe
  rw [hAttain] at hUpper
  have hLower := hR.1
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanSecondSpectralValueL2_eq_slem]
    at hLower
  exact le_antisymm hUpper hLower

/-- The absolute spectral gap equals the previously identified spectral gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanAbsoluteSpectralGapL2_eq_spectralGapL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 := by
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2]

/-- The exact finite-volume beta-zero random-scan relaxation time is `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRelaxationTimeL2_eq_324 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRelaxationTimeL2 = 324 := by
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRelaxationTimeL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- Compact receipt for the exact finite-volume beta-zero random-scan SLEM,
absolute spectral gap, relaxation time, and second-eigenspace multiplicity. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEMRelaxationTimeL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 =
      1 - (1 : ℝ) / 324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSLEML2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanAbsoluteSpectralGapL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRelaxationTimeL2 = 324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2

/-- The exact beta-zero random-scan SLEM and relaxation-time receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEMRelaxationTimeL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEMRelaxationTimeL2Receipt := by
  exact ⟨
    rfl,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSLEML2_isExact,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanAbsoluteSpectralGapL2_eq_spectralGapL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRelaxationTimeL2_eq_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanSecondEigenspaceL2⟩

end

end MathlibAnalytic
end MGAP4D
