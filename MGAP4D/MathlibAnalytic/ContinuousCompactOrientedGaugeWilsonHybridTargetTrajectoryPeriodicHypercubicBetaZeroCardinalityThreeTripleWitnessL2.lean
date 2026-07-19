import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroThreeLinkTripleModeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- There exists a third physical edge outside the canonical two-link pair. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityTwoPair :
    ∃ third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      third ∉
        ({periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} :
          Finset
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) := by
  by_contra hNo
  have hAll :
      ∀ edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        edge ∈
          ({periodicHypercubicThreeOriginAxisZeroTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} :
            Finset
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) := by
    intro edge
    by_contra hNot
    exact hNo ⟨edge, hNot⟩
  have hSub :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) ⊆
        {periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} := by
    intro edge _hEdge
    exact hAll edge
  have hCard := Finset.card_le_card hSub
  have hUnivCard :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hPairCard :
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        2 := by
    exact finset_pair_card_eq_two
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  rw [hUnivCard, hPairCard] at hCard
  norm_num at hCard

/-- A canonical noncomputably selected third physical edge. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.choose
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityTwoPair

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_not_mem :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ∉
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :=
  Classical.choose_spec
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityTwoPair

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ≠
      periodicHypercubicThreeOriginAxisZeroTarget := by
  intro hEq
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_not_mem
      (by
        rw [hEq]
        exact Finset.mem_insert_self _ _)

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget := by
  intro hEq
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_not_mem
      (by
        rw [hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The actual cardinality-three projector is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      3 ≠ 0 := by
  let source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  let third :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
  have hTargetSource :
      periodicHypercubicThreeOriginAxisZeroTarget ≠ source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  have hTargetThird :
      periodicHypercubicThreeOriginAxisZeroTarget ≠ third :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget.symm
  have hSourceThird : source ≠ third :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget.symm
  intro hZero
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          periodicHypercubicThreeOriginAxisZeroTarget source third))
    hZero
  have hProjectedZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          3
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
            periodicHypercubicThreeOriginAxisZeroTarget source third) = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_apply_threeLinkTripleMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget source third
      hTargetSource hTargetThird hSourceThird
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget source third
      hTargetSource hTargetThird hSourceThird
      (hProjectedSelf.symm.trans hProjectedZero)

/-- The actual cardinality-three joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_three_ne_bot :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      3 ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      3).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_ne_zero

/-- The nonzero cardinality-three projector realizes eigenvalue three through
the cardinality-sector criterion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_three_mem_heatBathPointSpectrumL2_of_cardinalityThreeProjector :
    (3 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      3
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_ne_zero

/-- Compact receipt for the actual beta-zero cardinality-three triple witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityThreeTripleWitnessL2Receipt :
    Prop :=
  periodicHypercubicThreeOriginAxisZeroTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ∧
  periodicHypercubicThreeOriginAxisZeroTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ∧
  periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      {periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      3
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      3 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      3 ≠ ⊥ ∧
  (3 : ℝ) ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The actual beta-zero cardinality-three triple-witness receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityThreeTripleWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityThreeTripleWitnessL2Receipt := by
  have hTargetSource :
      periodicHypercubicThreeOriginAxisZeroTarget ≠
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  have hTargetThird :
      periodicHypercubicThreeOriginAxisZeroTarget ≠
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget.symm
  have hSourceThird :
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ≠
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget.symm
  exact ⟨
    hTargetSource,
    hTargetThird,
    hSourceThird,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      hTargetSource hTargetThird hSourceThird,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeLinkTripleModeL2_mem_triple_fluctuationJointSector
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      hTargetSource hTargetThird hSourceThird,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_apply_threeLinkTripleMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      hTargetSource hTargetThird hSourceThird,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_three_ne_bot,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_three_mem_heatBathPointSpectrumL2_of_cardinalityThreeProjector⟩

end

end MathlibAnalytic
end MGAP4D
