import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityZeroVacuumWitnessL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRayleighInfimumAttainmentL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector fixed by one distinguished coordinate and killed by every other
coordinate belongs to the corresponding singleton joint sector. -/
theorem continuousLinearMap_mem_singleton_jointSectorSubmoduleL2_of_eq_self_of_eq_zero_of_ne
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target : ι)
    {f : V}
    (hTarget : Q target f = f)
    (hOther : ∀ source : ι, source ≠ target → Q source f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q {target} := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro source hSource
    have hEq : source = target := Finset.mem_singleton.mp hSource
    subst source
    exact hTarget
  · intro source hSource
    have hNe : source ≠ target := by
      simpa using hSource
    exact hOther source hNe

/-- The cardinality-one projector fixes every vector having a singleton
coordinate profile. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_one_apply_eq_self_of_singleton_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target : ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hTarget : Q target f = f)
    (hOther : ∀ source : ι, source ≠ target → Q source f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 1 hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q 1 {target} hComm (by simp)
      (continuousLinearMap_mem_singleton_jointSectorSubmoduleL2_of_eq_self_of_eq_zero_of_ne
        Q target hTarget hOther)

/-- A nonzero singleton-profile vector witnesses nonvanishing of the
cardinality-one projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_one_ne_zero_of_nonzero_singleton_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target : ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hTarget : Q target f = f)
    (hOther : ∀ source : ι, source ≠ target → Q source f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 1 hComm ≠ 0 := by
  intro hZero
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
  have hProjectedZero :
      continuousLinearMapCardinalitySectorProjectorL2 Q 1 hComm f = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    continuousLinearMap_cardinalitySectorProjectorL2_one_apply_eq_self_of_singleton_profile
      Q target hComm hTarget hOther
  exact hfNonzero (hProjectedSelf.symm.trans hProjectedZero)

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityOneSingletonEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The normalized actual one-link mode is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ≠ 0 := by
  intro hZero
  have hNorm :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one
  rw [hZero, norm_zero] at hNorm
  norm_num at hNorm

/-- The distinguished fluctuation projection fixes the normalized one-link
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_target_fluctuation_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2
  rw [map_smul,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_target_fluctuation_eq_self]

/-- Every other fluctuation projection annihilates the normalized one-link
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_fluctuation_eq_zero_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 = 0 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2
  rw [map_smul,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_fluctuation_eq_zero_of_ne
      source hSource,
    smul_zero]

/-- The normalized actual one-link mode belongs to the singleton joint sector
selected by the distinguished physical edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkUnitEigenvectorL2_mem_singleton_fluctuationJointSector :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget} := by
  classical
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMap_mem_singleton_jointSectorSubmoduleL2_of_eq_self_of_eq_zero_of_ne
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_target_fluctuation_eq_self
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_fluctuation_eq_zero_of_ne)

/-- The actual cardinality-one projector fixes the normalized one-link mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_apply_oneLinkUnitEigenvector_eq :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        1 periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      1 {periodicHypercubicThreeOriginAxisZeroTarget} (by simp)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkUnitEigenvectorL2_mem_singleton_fluctuationJointSector

/-- The actual cardinality-one projector is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      1 ≠ 0 := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_exists_nonzero_mem_fluctuationJointSector
      1).2
  exact ⟨
    {periodicHypercubicThreeOriginAxisZeroTarget},
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2,
    by simp,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkUnitEigenvectorL2_mem_singleton_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_ne_zero⟩

/-- The actual cardinality-one joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_one_ne_bot :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      1 ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      1).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_ne_zero

/-- The nonzero cardinality-one projector realizes eigenvalue one through the
cardinality-sector criterion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_heatBathPointSpectrumL2_of_cardinalityOneProjector :
    (1 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_ne_zero

/-- Compact receipt for the actual beta-zero cardinality-one singleton witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityOneSingletonWitnessL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∧
  (∀ source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
    source ≠ periodicHypercubicThreeOriginAxisZeroTarget →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 = 0) ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      {periodicHypercubicThreeOriginAxisZeroTarget} ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      1 periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      1 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      1 ≠ ⊥ ∧
  (1 : ℝ) ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The actual beta-zero cardinality-one singleton-witness receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityOneSingletonWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityOneSingletonWitnessL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_target_fluctuation_eq_self,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_fluctuation_eq_zero_of_ne,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkUnitEigenvectorL2_mem_singleton_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_apply_oneLinkUnitEigenvector_eq,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_one_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_one_ne_bot,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_heatBathPointSpectrumL2_of_cardinalityOneProjector⟩

end

end MathlibAnalytic
end MGAP4D
