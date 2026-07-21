import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFullSpectrumMultiplicityProfileL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroPointSpectrumAffineCorrespondenceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The actual beta-zero random-scan eigenspace at the affine cardinality value
`1 - k / 324`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
    (k : ℕ) :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  Module.End.genEigenspace
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2.toLinearMap
    (1 - (k : ℝ) / 324) 1

/-- The affine random-scan cardinality eigenspace is exactly the corresponding
heat-bath Hamiltonian cardinality eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2
    (k : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 k := by
  ext f
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    Module.End.mem_genEigenspace_one, Module.End.mem_genEigenspace_one]
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
      f (k : ℝ)).symm

/-- The cardinality projector range is also the affine random-scan eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324) :
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        k := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      k hk).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2
        k).symm

/-- The cardinality joint-sector sum is also the affine random-scan eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_randomScanCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        k := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      k hk).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2
        k).symm

/-- The stationary random-scan eigenspace has exact Cardinal rank one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_randomScanCardinalityEigenspaceL2_eq_one :
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
          0) =
      1 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one

/-- Every nonstationary affine random-scan cardinality eigenspace has rank at
least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanCardinalityEigenspaceL2_of_one_le
    (k : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
          k) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le
      k hLower hUpper

/-- Complete rank profile for every admissible affine random-scan cardinality
eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_rank_profile
    (k : ℕ)
    (hUpper : k ≤ 324) :
    (k = 0 ∧
      Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
            k) =
        1) ∨
    (1 ≤ k ∧
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
            k)) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceL2_rank_profile
      k hUpper

/-- The full actual beta-zero random-scan point spectrum. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 :
    Set ℝ :=
  {rho | ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
        rho • f}

/-- The affine 325-point grid for the normalized random-scan operator. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 :
    Set ℝ :=
  Set.range fun k : Fin 325 => 1 - (k.1 : ℝ) / 324

/-- The actual random-scan point spectrum is exactly the affine image of the
325-point heat-bath integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 := by
  ext rho
  constructor
  · rintro ⟨f, hf, hRandom⟩
    have hAffine :
        1 - ((324 : ℝ) * (1 - rho)) / 324 = rho := by
      ring
    have hHeat :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
          ((324 : ℝ) * (1 - rho)) • f := by
      apply
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
          f ((324 : ℝ) * (1 - rho))).mpr
      simpa [hAffine] using hRandom
    have hPoint :
        (324 : ℝ) * (1 - rho) ∈
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
      exact ⟨f, hf, hHeat⟩
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_allowed_integer_grid]
      at hPoint
    rcases hPoint with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hScalar :
        (324 : ℝ) * (1 - rho) = (k.1 : ℝ) := hk
    nlinarith
  · rintro ⟨k, rfl⟩
    have hPoint :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_le_324
        k.1 (by omega)
    change ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
          (k.1 : ℝ) • f at hPoint
    rcases hPoint with ⟨f, hf, hHeat⟩
    exact ⟨f, hf,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
        f (k.1 : ℝ)).mp hHeat⟩

/-- Every actual beta-zero random-scan point-spectrum value carries the complete
rank profile of its unique affine cardinality sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_exists_index_with_rank_profile
    (rho : ℝ)
    (hRho : rho ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2) :
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
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid]
    at hRho
  rcases hRho with ⟨k, rfl⟩
  refine ⟨k, rfl, ?_⟩
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_rank_profile
      k.1 (by omega)

/-- Compact receipt for the complete finite-volume beta-zero random-scan
point-spectrum multiplicity profile. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMultiplicityProfileL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedRandomScanPointSpectrumL2 ∧
    (∀ k : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2 k =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 k) ∧
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

/-- The complete beta-zero random-scan multiplicity receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMultiplicityProfileL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanMultiplicityProfileL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCardinalityEigenspaceL2_eq_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_randomScanCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_randomScanCardinalityEigenspaceL2_of_one_le,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_randomScanCardinalityEigenspaceL2⟩

end

end MathlibAnalytic
end MGAP4D
