import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroAllCardinalityEigenspacesInfiniteRankL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroZeroEigenspaceMultiplicityOneL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Every positive actual beta-zero heat-bath cardinality eigenspace, from
cardinality one through the full 324-edge sector, has Cardinal rank at least
`aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le
    (k : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k) := by
  by_cases hFour : 4 ≤ k
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_four_le
        k hFour hUpper
  · have hk : k = 1 ∨ k = 2 ∨ k = 3 := by
      omega
    rcases hk with rfl | rfl | rfl
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_heatBathCardinalityEigenspaceL2
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_heatBathCardinalityEigenspaceL2

/-- The range of every positive actual beta-zero cardinality projector, from
one through 324, has Cardinal rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_fluctuationCardinalityProjectorL2_of_one_le
    (k : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap) := by
  have hEdgeCard :
      Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hkCard :
      k ≤ Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    omega
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      k hkCard]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le
      k hLower hUpper

/-- Every positive actual beta-zero cardinality joint-sector sum, from one
through 324, has Cardinal rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2_of_one_le
    (k : ℕ)
    (hLower : 1 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          k) := by
  have hEdgeCard :
      Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hkCard :
      k ≤ Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    omega
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      k hkCard]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le
      k hLower hUpper

/-- Complete rank profile for every admissible beta-zero heat-bath cardinality
eigenspace: cardinality zero has exact rank one, while every positive
cardinality has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceL2_rank_profile
    (k : ℕ)
    (hUpper : k ≤ 324) :
    (k = 0 ∧
      Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
            k) =
        1) ∨
    (1 ≤ k ∧
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
            k)) := by
  by_cases hZero : k = 0
  · subst k
    exact Or.inl ⟨rfl,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one⟩
  · right
    have hLower : 1 ≤ k := by
      omega
    exact ⟨hLower,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le
        k hLower hUpper⟩

/-- Complete rank profile for every admissible beta-zero cardinality-projector
range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_range_rank_profile
    (k : ℕ)
    (hUpper : k ≤ 324) :
    (k = 0 ∧
      Module.rank ℝ
          (LinearMap.range
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              k).toLinearMap) =
        1) ∨
    (1 ≤ k ∧
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (LinearMap.range
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              k).toLinearMap)) := by
  by_cases hZero : k = 0
  · subst k
    exact Or.inl ⟨rfl,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_range_zero_fluctuationCardinalityProjectorL2_eq_one⟩
  · right
    have hLower : 1 ≤ k := by
      omega
    exact ⟨hLower,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_fluctuationCardinalityProjectorL2_of_one_le
        k hLower hUpper⟩

/-- Complete rank profile for every admissible beta-zero cardinality joint-sector
sum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_rank_profile
    (k : ℕ)
    (hUpper : k ≤ 324) :
    (k = 0 ∧
      Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
            k) =
        1) ∨
    (1 ≤ k ∧
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
            k)) := by
  by_cases hZero : k = 0
  · subst k
    exact Or.inl ⟨rfl,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_one⟩
  · right
    have hLower : 1 ≤ k := by
      omega
    exact ⟨hLower,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2_of_one_le
        k hLower hUpper⟩

/-- Every actual beta-zero point-spectrum value has a unique admissible integer
index carrying the complete rank profile: the vacuum value has rank one and
every positive spectral value has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_exists_index_with_rank_profile
    (lam : ℝ)
    (hLam : lam ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2) :
    ∃ k : Fin 325,
      lam = (k.1 : ℝ) ∧
        ((k.1 = 0 ∧
            Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
                  k.1) =
              1) ∨
          (1 ≤ k.1 ∧
            Cardinal.aleph0 ≤
              Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
                  k.1))) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_allowed_integer_grid]
    at hLam
  rcases hLam with ⟨k, rfl⟩
  refine ⟨k, rfl, ?_⟩
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceL2_rank_profile
      k.1 (by omega)

/-- Every actual beta-zero full-spectrum value has the same complete
multiplicity profile, because the full spectrum equals the point spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_exists_index_with_rank_profile
    (lam : ℝ)
    (hLam : lam ∈
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) :
    ∃ k : Fin 325,
      lam = (k.1 : ℝ) ∧
        ((k.1 = 0 ∧
            Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
                  k.1) =
              1) ∨
          (1 ≤ k.1 ∧
            Cardinal.aleph0 ≤
              Module.rank ℝ
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
                  k.1))) := by
  rw [←
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_heatBathSpectrumL2]
    at hLam
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_exists_index_with_rank_profile
      lam hLam

/-- Compact receipt for the complete finite-volume beta-zero spectral
multiplicity profile. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumMultiplicityProfileL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 ∧
    spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 =
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 ∧
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          0) =
      1 ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 324 →
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
            k)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 324 →
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (LinearMap.range
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              k).toLinearMap)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 324 →
      Cardinal.aleph0 ≤
        Module.rank ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
            k))

/-- The complete finite-volume beta-zero spectral multiplicity receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumMultiplicityProfileL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumMultiplicityProfileL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_allowed_integer_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_eq_allowed_integer_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_heatBathSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_one_le,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_fluctuationCardinalityProjectorL2_of_one_le,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2_of_one_le⟩

end

end MathlibAnalytic
end MGAP4D
