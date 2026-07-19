import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFiniteSetProductModeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_allCardinalityEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- Every natural cardinality up to the actual 324-link edge count is realized
by a finite selected set. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_finset_card_eq_of_le_324
    (k : ℕ)
    (hk : k ≤ 324) :
    ∃ s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      s.card = k := by
  have hUnivCard :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hkUniv :
      k ≤
        (Finset.univ :
          Finset
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card := by
    rw [hUnivCard]
    exact hk
  obtain ⟨s, _hsSub, hsCard⟩ :=
    Finset.exists_subset_card_eq hkUniv
  exact ⟨s, hsCard⟩

/-- For every `k ≤ 324`, a concrete finite-set product mode gives a nonzero
vector in a `k`-coordinate joint sector and is fixed by `E_k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_finiteSetProductMode_witness_of_le_324
    (k : ℕ)
    (hk : k ≤ 324) :
    ∃ s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      s.card = k ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          s ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s := by
  obtain ⟨s, hsCard⟩ :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_finset_card_eq_of_le_324
      k hk
  refine ⟨s, hsCard, ?_, ?_, ?_⟩
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_ne_zero
        s
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_finiteSetProductModeL2_mem_fluctuationJointSector
        s
  · simpa [hsCard] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_apply_finiteSetProductMode_eq
        s

/-- Every actual beta-zero cardinality projector `E_k`, for `k ≤ 324`, is
nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_of_le_324
    (k : ℕ)
    (hk : k ≤ 324) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      k ≠ 0 := by
  obtain ⟨s, hsCard⟩ :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_finset_card_eq_of_le_324
      k hk
  simpa [hsCard] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_ne_zero
      s

/-- Every actual beta-zero cardinality joint-sector sum, for `k ≤ 324`, is
non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_ne_bot_of_le_324
    (k : ℕ)
    (hk : k ≤ 324) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      k ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      k).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_of_le_324
        k hk)

/-- Every integer grid point `k = 0, ..., 324` occurs in the actual beta-zero
heat-bath point spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_le_324
    (k : ℕ)
    (hk : k ≤ 324) :
    (k : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      k
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_of_le_324
        k hk)

/-- Compact receipt for the complete finite-volume beta-zero cardinality grid. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityFiniteSetProductWitnessL2Receipt :
    Prop :=
  ∀ k : ℕ,
    k ≤ 324 →
      (∃ s : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        s.card = k ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ≠ 0 ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ∈
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
            s ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        k ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k ≠ ⊥ ∧
      (k : ℝ) ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The complete finite-volume beta-zero cardinality-grid receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityFiniteSetProductWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityFiniteSetProductWitnessL2Receipt := by
  intro k hk
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_finiteSetProductMode_witness_of_le_324
      k hk,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_of_le_324
      k hk,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_ne_bot_of_le_324
      k hk,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_le_324
      k hk⟩

end

end MathlibAnalytic
end MGAP4D
