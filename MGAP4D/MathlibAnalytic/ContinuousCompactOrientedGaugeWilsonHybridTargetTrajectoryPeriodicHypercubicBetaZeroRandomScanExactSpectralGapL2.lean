import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanFullSpectrumMultiplicityProfileL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- In a finite affine grid `1 - k / N`, every nonstationary index has gap at
least `N⁻¹` from the stationary value `1`. -/
theorem fin_affine_grid_inv_le_gap_of_ne_zero
    (N : ℕ)
    (hN : 0 < N)
    (k : Fin (N + 1))
    (hk : k.1 ≠ 0) :
    (N : ℝ)⁻¹ ≤ 1 - (1 - (k.1 : ℝ) / N) := by
  have hkNat : 1 ≤ k.1 := Nat.one_le_iff_ne_zero.mpr hk
  have hkReal : (1 : ℝ) ≤ (k.1 : ℝ) := by
    exact_mod_cast hkNat
  have hNReal : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hInv : 0 ≤ (N : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hNReal)
  calc
    (N : ℝ)⁻¹ = 1 * (N : ℝ)⁻¹ := by rw [one_mul]
    _ ≤ (k.1 : ℝ) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hkReal hInv
    _ = 1 - (1 - (k.1 : ℝ) / N) := by
      rw [div_eq_mul_inv]
      ring

/-- The exact finite-volume beta-zero random-scan spectral gap. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 : ℝ :=
  (1 : ℝ) / 324

/-- The largest nonstationary beta-zero random-scan spectral value. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 : ℝ :=
  1 - (1 : ℝ) / 324

/-- The eigenspace of the largest nonstationary beta-zero random-scan spectral
value. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  Module.End.genEigenspace
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2.toLinearMap
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2
    1

/-- A scalar is an exact nonstationary spectral gap when it lower-bounds every
gap from `1` and that lower bound is attained by a nonstationary spectral
value. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSpectralGapL2
    (delta : ℝ) : Prop :=
  (∀ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
      rho ≠ 1 →
      delta ≤ 1 - rho) ∧
    ∃ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
      rho ≠ 1 ∧
      1 - rho = delta

/-- The second spectral value belongs to the full beta-zero random-scan
operator spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
  exact ⟨⟨1, by omega⟩, rfl⟩

/-- The second spectral value is genuinely nonstationary. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ≠ 1 := by
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2]

/-- Every nonstationary full-spectrum value lies at distance at least `1 / 324`
from the stationary value `1`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_le_one_sub_of_mem_spectrum_of_ne_one
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2)
    (hNe : rho ≠ 1) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 ≤
      1 - rho := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
    at hRho
  rcases hRho with ⟨k, rfl⟩
  have hk : k.1 ≠ 0 := by
    intro hkZero
    apply hNe
    simp [hkZero]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2,
    one_div] using
      fin_affine_grid_inv_le_gap_of_ne_zero 324 (by omega) k hk

/-- Equivalently, every nonstationary full-spectrum value is at most
`1 - 1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_le_second_of_ne_one
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2)
    (hNe : rho ≠ 1) :
    rho ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_le_one_sub_of_mem_spectrum_of_ne_one
      rho hRho hNe
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2]
    at hGap ⊢
  linarith

/-- The second spectral value attains the gap `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_sub_randomScanSecondSpectralValueL2_eq_spectralGapL2 :
    1 - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 := by
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2]

/-- The value `1 / 324` is the exact nonstationary beta-zero random-scan
spectral gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_isExact :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSpectralGapL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 := by
  constructor
  · intro rho hRho hNe
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_le_one_sub_of_mem_spectrum_of_ne_one
        rho hRho hNe
  · exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_sub_randomScanSecondSpectralValueL2_eq_spectralGapL2⟩

/-- Any scalar satisfying the exact-gap characterization is necessarily
`1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanIsExactSpectralGapL2_unique
    {delta : ℝ}
    (hDelta :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSpectralGapL2
        delta) :
    delta = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 := by
  rcases hDelta.2 with ⟨rho, hRho, hNe, hAttain⟩
  have hLower :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_le_one_sub_of_mem_spectrum_of_ne_one
      rho hRho hNe
  have hUpper := hDelta.1
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_sub_randomScanSecondSpectralValueL2_eq_spectralGapL2]
    at hUpper
  linarith

/-- The second eigenspace is the cardinality-one random-scan eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        1 := by
  rfl

/-- The eigenspace at the second spectral value has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanSecondEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanCardinalityEigenspaceL2_of_one_le
      1 (by omega) (by omega)

/-- Compact receipt for the exact finite-volume beta-zero random-scan spectral
gap and its multiplicity profile. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactSpectralGapL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 =
      (1 : ℝ) / 324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 =
      1 - (1 : ℝ) / 324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ≠ 1 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactSpectralGapL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralGapL2 ∧
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
          0) =
      1 ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2

/-- The exact beta-zero random-scan spectral-gap receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactSpectralGapL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactSpectralGapL2Receipt := by
  exact ⟨
    rfl,
    rfl,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_mem_spectrum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondSpectralValueL2_ne_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectralGapL2_isExact,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_randomScanCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanSecondEigenspaceL2⟩

end

end MathlibAnalytic
end MGAP4D
