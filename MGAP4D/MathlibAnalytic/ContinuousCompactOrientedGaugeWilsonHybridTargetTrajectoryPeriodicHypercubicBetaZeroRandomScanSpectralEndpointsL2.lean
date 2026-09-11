import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSLEMRelaxationTimeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Every value in a positive finite affine grid `1 - k / N` is at most the
stationary endpoint `1`. -/
theorem fin_affine_grid_le_one
    (N : ℕ)
    (hN : 0 < N)
    (k : Fin (N + 1)) :
    1 - (k.1 : ℝ) / N ≤ 1 := by
  have hNReal : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hkNonneg : (0 : ℝ) ≤ (k.1 : ℝ) := by
    positivity
  have hDivNonneg : 0 ≤ (k.1 : ℝ) / (N : ℝ) :=
    div_nonneg hkNonneg (le_of_lt hNReal)
  linarith

/-- The minimum spectral endpoint of the actual finite-volume beta-zero
random-scan operator. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2 : ℝ :=
  0

/-- The maximum spectral endpoint of the actual finite-volume beta-zero
random-scan operator. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2 : ℝ :=
  1

/-- The eigenspace at the minimum spectral endpoint `0`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  Module.End.genEigenspace
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2.toLinearMap
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2
    1

/-- A scalar is an exact minimum spectral endpoint when it belongs to the full
spectrum and lower-bounds every full-spectrum value. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMinimumSpectralValueL2
    (m : ℝ) : Prop :=
  m ∈ spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
    ∀ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
      m ≤ rho

/-- A scalar is an exact maximum spectral endpoint when it belongs to the full
spectrum and upper-bounds every full-spectrum value. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMaximumSpectralValueL2
    (M : ℝ) : Prop :=
  M ∈ spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
    ∀ rho : ℝ,
      rho ∈ spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 →
      rho ≤ M

/-- The bottom endpoint `0` belongs to the full beta-zero random-scan spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMinimumSpectralValueL2_mem_spectrum :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2 ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
  refine ⟨⟨324, by omega⟩, ?_⟩
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2]

/-- The stationary endpoint `1` belongs to the full beta-zero random-scan
spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMaximumSpectralValueL2_mem_spectrum :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2 ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
  refine ⟨⟨0, by omega⟩, ?_⟩
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2]

/-- Every full-spectrum value lies in the closed interval `[0, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2) :
    rho ∈ Set.Icc (0 : ℝ) 1 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]
    at hRho
  rcases hRho with ⟨k, rfl⟩
  exact ⟨
    fin_affine_grid_nonneg 324 (by omega) k,
    fin_affine_grid_le_one 324 (by omega) k⟩

/-- The full beta-zero random-scan spectrum is contained in `[0, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_subset_Icc_zero_one :
    spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ⊆
      Set.Icc (0 : ℝ) 1 := by
  intro rho hRho
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
      rho hRho

/-- The value `0` is the exact minimum beta-zero random-scan spectral endpoint. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMinimumSpectralValueL2_isExact :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMinimumSpectralValueL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2 := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMinimumSpectralValueL2_mem_spectrum
  · intro rho hRho
    have hInterval :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
        rho hRho
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2]
      using hInterval.1

/-- The value `1` is the exact maximum beta-zero random-scan spectral endpoint. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMaximumSpectralValueL2_isExact :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMaximumSpectralValueL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2 := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMaximumSpectralValueL2_mem_spectrum
  · intro rho hRho
    have hInterval :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
        rho hRho
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2]
      using hInterval.2

/-- The exact-minimum characterization determines the bottom endpoint uniquely. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanIsExactMinimumSpectralValueL2_unique
    {m : ℝ}
    (hMin :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMinimumSpectralValueL2
        m) :
    m = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2 := by
  have hZeroLe : (0 : ℝ) ≤ m :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
      m hMin.1).1
  have hLeZero : m ≤ (0 : ℝ) := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2]
      using hMin.2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMinimumSpectralValueL2_mem_spectrum
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2
  exact le_antisymm hLeZero hZeroLe

/-- The exact-maximum characterization determines the top endpoint uniquely. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanIsExactMaximumSpectralValueL2_unique
    {M : ℝ}
    (hMax :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMaximumSpectralValueL2
        M) :
    M = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2 := by
  have hMLeOne : M ≤ (1 : ℝ) :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_mem_Icc_zero_one
      M hMax.1).2
  have hOneLeM : (1 : ℝ) ≤ M := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2]
      using hMax.2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMaximumSpectralValueL2_mem_spectrum
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2
  exact le_antisymm hMLeOne hOneLeM

/-- The zero eigenspace is the terminal cardinality-324 random-scan eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        324 := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2]

/-- The eigenspace at the minimum spectral endpoint has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanZeroEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanCardinalityEigenspaceL2_of_one_le
      324 (by omega) (by omega)

/-- The terminal cardinality projector range is exactly the zero eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_324_eq_randomScanZeroEigenspaceL2 :
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          324).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 := by
  calc
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          324).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        324 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2
        324 (by omega)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324.symm

/-- The terminal joint-sector sum is exactly the zero eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_324_eq_randomScanZeroEigenspaceL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        324 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        324 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        324 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_randomScanCardinalityEigenspaceL2
        324 (by omega)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanZeroEigenspaceL2_eq_cardinality324.symm

/-- Compact receipt for the exact beta-zero random-scan spectral endpoints and
bottom-eigenspace multiplicity profile. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralEndpointsL2Receipt :
    Prop :=
  spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ⊆
    Set.Icc (0 : ℝ) 1 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMinimumSpectralValueL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMinimumSpectralValueL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanIsExactMaximumSpectralValueL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMaximumSpectralValueL2 ∧
  Module.rank ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        0) =
    1 ∧
  Cardinal.aleph0 ≤
    Module.rank ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 ∧
  LinearMap.range
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        324).toLinearMap =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      324 =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanZeroEigenspaceL2

/-- The exact beta-zero random-scan spectral-endpoint receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralEndpointsL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSpectralEndpointsL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_subset_Icc_zero_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMinimumSpectralValueL2_isExact,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanMaximumSpectralValueL2_isExact,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_randomScanCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanZeroEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_324_eq_randomScanZeroEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_324_eq_randomScanZeroEigenspaceL2⟩

end

end MathlibAnalytic
end MGAP4D
