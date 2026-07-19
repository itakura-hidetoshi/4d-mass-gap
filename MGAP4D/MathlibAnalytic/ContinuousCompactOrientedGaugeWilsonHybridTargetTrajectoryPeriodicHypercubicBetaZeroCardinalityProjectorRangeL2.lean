import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalitySpectralResolutionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The algebraic sum of all joint sectors whose labels have cardinality `k`. -/
noncomputable def continuousLinearMapCardinalityJointSectorSumSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ) :
    Submodule ℝ V :=
  ⨆ s : {s : Finset ι //
      s ∈ (Finset.univ : Finset ι).powersetCard k},
    continuousLinearMapJointSectorSubmoduleL2 Q s.1

/-- A joint sector of cardinality `k` is contained in the corresponding
cardinality-sector sum. -/
theorem continuousLinearMap_jointSectorSubmoduleL2_le_cardinalityJointSectorSumSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (s : Finset ι)
    (hs : s ∈ (Finset.univ : Finset ι).powersetCard k) :
    continuousLinearMapJointSectorSubmoduleL2 Q s ≤
      continuousLinearMapCardinalityJointSectorSumSubmoduleL2 Q k := by
  exact le_iSup_of_le ⟨s, hs⟩ le_rfl

/-- Pointwise expansion of the cardinality projector into the canonical
joint-sector projectors of the same weight. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_sum_jointSectorProjectorsL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (f : V) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f =
      ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        continuousLinearMapJointSectorProjectorL2 Q s hComm f := by
  classical
  simp [continuousLinearMapCardinalitySectorProjectorL2]

/-- Every cardinality-projected vector belongs to the algebraic sum of the
matching joint sectors. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_apply_mem_cardinalityJointSectorSumSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (f : V) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f ∈
      continuousLinearMapCardinalityJointSectorSumSubmoduleL2 Q k := by
  classical
  rw [continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_sum_jointSectorProjectorsL2]
  apply Finset.sum_mem
  intro s hs
  apply
    continuousLinearMap_jointSectorSubmoduleL2_le_cardinalityJointSectorSumSubmoduleL2
      Q k s hs
  exact
    continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
      Q s hIdempotent hComm f

/-- The cardinality projector restricts to the identity on every joint sector
with matching cardinality. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hsCard : s.card = k)
    {f : V}
    (hf : f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f = f := by
  classical
  have hs : s ∈ (Finset.univ : Finset ι).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hsCard⟩
  rw [continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_sum_jointSectorProjectorsL2]
  rw [Finset.sum_eq_single s]
  · exact
      continuousLinearMap_jointSectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
        Q s hComm hf
  · intro t ht hts
    exact
      continuousLinearMap_jointSectorProjectorL2_apply_eq_zero_of_mem_jointSectorSubmoduleL2_of_ne
        Q t s hComm hts hf
  · intro hsNot
    exact (hsNot hs).elim

/-- The range of the weight-`k` projector is exactly the algebraic sum of the
joint sectors having cardinality `k`. -/
theorem continuousLinearMap_range_cardinalitySectorProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    LinearMap.range
        (continuousLinearMapCardinalitySectorProjectorL2 Q k hComm).toLinearMap =
      continuousLinearMapCardinalityJointSectorSumSubmoduleL2 Q k := by
  classical
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨g, rfl⟩
    exact
      continuousLinearMap_cardinalitySectorProjectorL2_apply_mem_cardinalityJointSectorSumSubmoduleL2
        Q k hIdempotent hComm g
  · refine iSup_le ?_
    intro s
    intro f hf
    refine ⟨f, ?_⟩
    change continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f = f
    exact
      continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
        Q k s.1 hComm (Finset.mem_powersetCard.mp s.2).2 hf

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityRangeEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The algebraic sum of the actual beta-zero joint sectors with cardinality
`k`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
    (k : ℕ) :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  ⨆ s : {s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge //
      s ∈ (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powersetCard k},
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      s.1

/-- Pointwise expansion of the actual cardinality projector into the actual
canonical joint-sector projectors of the same weight. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_sum_jointSectorProjectorsL2
    (k : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f =
      ∑ s ∈ (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powersetCard k,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using
      (continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_sum_jointSectorProjectorsL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k
        (fun target source g =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source g)
        f)

/-- The actual cardinality projector is the identity on every actual joint
sector whose label has the same cardinality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
    (k : ℕ)
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hsCard : s.card = k)
    {f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure}
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f =
      f := by
  classical
  have hfGeneric :
      f ∈ continuousLinearMapJointSectorSubmoduleL2
        (fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        s := by
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
      using hf
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2]
    using
      (continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k s
        (fun target source g =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source g)
        hsCard hfGeneric)

/-- The range of the actual beta-zero cardinality projector is exactly the
algebraic sum of the actual joint sectors of that cardinality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
    (k : ℕ) :
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2,
    ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMap_range_cardinalitySectorProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k
        (fun edge g =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge g)
        (fun target source g =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source g))

/-- Compact receipt for the actual beta-zero cardinality-projector range
characterization. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorRangeL2Receipt :
    Prop :=
  (∀ (k : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f =
      ∑ s ∈ (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powersetCard k,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          s f) ∧
  (∀ (k : ℕ)
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    s.card = k →
    f ∈ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      s →
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f = f) ∧
  ∀ k : ℕ,
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k

/-- The actual beta-zero cardinality-projector range characterization receipt
is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorRangeL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorRangeL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_sum_jointSectorProjectorsL2,
    fun k s f hsCard hf =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
        k s hsCard hf,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
