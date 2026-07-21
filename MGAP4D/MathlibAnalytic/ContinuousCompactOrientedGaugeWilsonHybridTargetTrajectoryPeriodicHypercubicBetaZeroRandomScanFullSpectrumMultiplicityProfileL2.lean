import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanMultiplicityProfileL2
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped Pointwise
open ContinuousCompactRandomScanL2Structure

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Generic affine spectral mapping for a continuous linear endomorphism and a
nonzero scalar: the spectrum of `I - cT` is `{1} - c • spectrum T`. -/
theorem continuousLinearMap_spectrum_one_sub_smul_eq_singleton_sub_smul
    (T : V →L[ℝ] V)
    (c : ℝ)
    (hc : c ≠ 0) :
    spectrum ℝ (1 - c • T) =
      ({1} : Set ℝ) - c • spectrum ℝ T := by
  calc
    spectrum ℝ (1 - c • T) =
        ({1} : Set ℝ) - spectrum ℝ (c • T) := by
      simpa using (spectrum.singleton_sub_eq (c • T) (1 : ℝ)).symm
    _ = ({1} : Set ℝ) - c • spectrum ℝ T := by
      rw [show spectrum ℝ (c • T) = c • spectrum ℝ T by
        simpa [Units.smul_def] using
          (spectrum.unit_smul_eq_smul T (Units.mk0 c hc))]

/-- Pointwise affine transport of a ranged scalar family. -/
theorem singleton_sub_smul_range_eq_range_one_sub_smul
    {ι : Type*}
    (c : ℝ)
    (f : ι → ℝ) :
    ({1} : Set ℝ) - c • Set.range f =
      Set.range (fun i => 1 - c • f i) := by
  rw [← Set.range_smul, Set.singleton_sub, Set.image_range]

/-- The normalized random-scan operator is the affine continuous-linear-map
expression `I - 324⁻¹ H_HB`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_eq_one_sub_inv324_smul_heatBathHamiltonianL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 =
      1 - (324 : ℝ)⁻¹ •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  have hEdge : 0 < Fintype.card C.base.geometry.Edge := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    norm_num
  apply ContinuousLinearMap.ext
  intro f
  change C.randomScanHeatBathL2 f =
    f - (324 : ℝ)⁻¹ • C.heatBathHamiltonianL2 f
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    using
      (continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
        C hEdge f)

/-- The affine image of the heat-bath integer grid is exactly the allowed
325-point random-scan grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_singleton_sub_inv324_smul_allowedHeatBathPointSpectrumL2_eq_allowedRandomScanPointSpectrumL2 :
    ({1} : Set ℝ) - (324 : ℝ)⁻¹ •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2
  rw [singleton_sub_smul_range_eq_range_one_sub_smul]
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2
  congr 1
  funext k
  change 1 - (324 : ℝ)⁻¹ * (k.1 : ℝ) =
    1 - (k.1 : ℝ) / 324
  ring

/-- The full operator spectrum of the actual beta-zero normalized random-scan
operator is exactly its 325-point affine grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid :
    spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_eq_one_sub_inv324_smul_heatBathHamiltonianL2]
  calc
    spectrum ℝ
        (1 - (324 : ℝ)⁻¹ •
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) =
      ({1} : Set ℝ) - (324 : ℝ)⁻¹ •
        spectrum ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 :=
      continuousLinearMap_spectrum_one_sub_smul_eq_singleton_sub_smul
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (324 : ℝ)⁻¹
        (by norm_num)
    _ = ({1} : Set ℝ) - (324 : ℝ)⁻¹ •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_eq_allowed_integer_grid]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_singleton_sub_inv324_smul_allowedHeatBathPointSpectrumL2_eq_allowedRandomScanPointSpectrumL2

/-- For the actual beta-zero random-scan operator, the point spectrum exhausts
the full operator spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_randomScanSpectrumL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 =
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid]

/-- Every full-spectrum value of the actual beta-zero random-scan operator has
a unique affine cardinality index carrying the complete rank profile. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_exists_index_with_rank_profile
    (rho : ℝ)
    (hRho : rho ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2) :
    ∃ k : Fin 325,
      rho = 1 - (k.1 : ℝ) / 324 ∧
        ((k.1 = 0 ∧
            Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
                  k.1) =
              1) ∨
          (1 ≤ k.1 ∧
            Cardinal.aleph0 ≤
              Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
                  k.1))) := by
  rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_randomScanSpectrumL2]
    at hRho
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_exists_index_with_rank_profile
      rho hRho

/-- Compact receipt for the complete finite-volume beta-zero random-scan full
spectrum and multiplicity profile. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFullSpectrumMultiplicityProfileL2Receipt :
    Prop :=
  spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 =
    spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ∧
  Module.rank ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        0) =
    1 ∧
  (∀ k : ℕ, 1 ≤ k → k ≤ 324 →
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
          k)) ∧
  (∀ k : ℕ, k ≤ 324 →
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        k) ∧
  (∀ k : ℕ, k ≤ 324 →
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        k)

/-- The complete beta-zero random-scan full-spectrum multiplicity receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFullSpectrumMultiplicityProfileL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFullSpectrumMultiplicityProfileL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSpectrumL2_eq_allowed_affine_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_randomScanSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_randomScanCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanCardinalityEigenspaceL2_of_one_le,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_randomScanCardinalityEigenspaceL2⟩

end

end MathlibAnalytic
end MGAP4D
