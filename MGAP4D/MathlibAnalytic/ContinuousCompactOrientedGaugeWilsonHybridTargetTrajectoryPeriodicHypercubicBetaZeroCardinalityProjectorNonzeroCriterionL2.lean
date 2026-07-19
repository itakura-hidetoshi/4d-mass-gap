import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityProjectorRangeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A cardinality projector is the zero operator exactly when the algebraic sum
of its matching joint sectors is the bottom submodule. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm = 0 ↔
      continuousLinearMapCardinalityJointSectorSumSubmoduleL2 Q k = ⊥ := by
  classical
  constructor
  · intro hZero
    rw [← continuousLinearMap_range_cardinalitySectorProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
      Q k hIdempotent hComm]
    ext f
    constructor
    · intro hf
      rcases hf with ⟨g, hg⟩
      have hApply := congrArg (fun T : V →L[ℝ] V => T g) hZero
      have hEg : continuousLinearMapCardinalitySectorProjectorL2 Q k hComm g = 0 := by
        simpa using hApply
      have hfZero : f = 0 := hg.symm.trans hEg
      simpa [hfZero]
    · intro hf
      have hfZero : f = 0 := by
        simpa using hf
      subst f
      exact ⟨0, by simp⟩
  · intro hBot
    apply ContinuousLinearMap.ext
    intro f
    change continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f = 0
    have hfMem :=
      continuousLinearMap_cardinalitySectorProjectorL2_apply_mem_cardinalityJointSectorSumSubmoduleL2
        Q k hIdempotent hComm f
    have hfBot :
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f ∈
          (⊥ : Submodule ℝ V) := by
      rw [← hBot]
      exact hfMem
    simpa using hfBot

/-- Negating the zero criterion gives the exact nonzero criterion in terms of the
matching joint-sector sum. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm ≠ 0 ↔
      continuousLinearMapCardinalityJointSectorSumSubmoduleL2 Q k ≠ ⊥ := by
  exact not_congr
    (continuousLinearMap_cardinalitySectorProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
      Q k hIdempotent hComm)

/-- A cardinality projector is nonzero exactly when one matching joint sector
contains a nonzero vector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_ne_zero_iff_exists_nonzero_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm ≠ 0 ↔
      ∃ (s : Finset ι) (f : V),
        s.card = k ∧
        f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s ∧
        f ≠ 0 := by
  classical
  constructor
  · intro hNonzero
    have hApply :
        ∃ f : V,
          continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f ≠ 0 := by
      by_contra hNoApply
      push_neg at hNoApply
      apply hNonzero
      apply ContinuousLinearMap.ext
      intro f
      simpa using hNoApply f
    rcases hApply with ⟨f, hfNonzero⟩
    have hSummand :
        ∃ s ∈ (Finset.univ : Finset ι).powersetCard k,
          continuousLinearMapJointSectorProjectorL2 Q s hComm f ≠ 0 := by
      by_contra hNoSummand
      push_neg at hNoSummand
      apply hfNonzero
      rw [continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_sum_jointSectorProjectorsL2]
      exact Finset.sum_eq_zero hNoSummand
    rcases hSummand with ⟨s, hs, hsNonzero⟩
    exact ⟨
      s,
      continuousLinearMapJointSectorProjectorL2 Q s hComm f,
      (Finset.mem_powersetCard.mp hs).2,
      continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
        Q s hIdempotent hComm f,
      hsNonzero⟩
  · rintro ⟨s, f, hsCard, hfSector, hfNonzero⟩ hZero
    have hSelf :=
      continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
        Q k s hComm hsCard hfSector
    have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
    have hZeroApply :
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f = 0 := by
      simpa using hApply
    exact hfNonzero (hSelf.symm.trans hZeroApply)

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityNonzeroEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The actual beta-zero cardinality projector is zero exactly when the sum of
its matching actual joint sectors is bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
    (k : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k = ⊥ := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2,
    continuousLinearMapCardinalityJointSectorSumSubmoduleL2,
    ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMap_cardinalitySectorProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- The actual beta-zero cardinality projector is nonzero exactly when its
matching actual joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
    (k : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k ≠ ⊥ := by
  exact not_congr
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
      k)

/-- The actual beta-zero cardinality projector is nonzero exactly when an actual
joint sector of that cardinality contains a nonzero Gibbs `L²` vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_exists_nonzero_mem_fluctuationJointSector
    (k : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0 ↔
      ∃ (s : Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
        s.card = k ∧
        f ∈ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          s ∧
        f ≠ 0 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMap_cardinalitySectorProjectorL2_ne_zero_iff_exists_nonzero_mem_jointSectorSubmoduleL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Nonvanishing of an actual cardinality projector realizes its cardinality as
an actual beta-zero heat-bath point-spectrum value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
    (k : ℕ)
    (hNonzero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0) :
    (k : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  rcases
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_exists_nonzero_mem_fluctuationJointSector
        k).1 hNonzero with
    ⟨s, f, hsCard, hfSector, hfNonzero⟩
  have hSpectrum :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_heatBathPointSpectrumL2_of_nonzero_mem_fluctuationJointSector
      s hfNonzero hfSector
  simpa [hsCard] using hSpectrum

/-- Compact receipt for the actual cardinality-projector zero, nonzero, witness,
and point-spectrum criteria. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorNonzeroCriterionL2Receipt :
    Prop :=
  ∀ k : ℕ,
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k = ⊥) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k ≠ ⊥) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0 ↔
      ∃ (s : Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
        s.card = k ∧
        f ∈ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          s ∧
        f ≠ 0) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k ≠ 0 →
      (k : ℝ) ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2)

/-- The actual beta-zero cardinality-projector nonzero-criterion receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorNonzeroCriterionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorNonzeroCriterionL2Receipt := by
  intro k
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_eq_zero_iff_cardinalityJointSectorSumSubmoduleL2_eq_bot
      k,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      k,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_exists_nonzero_mem_fluctuationJointSector
      k,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      k⟩

end

end MathlibAnalytic
end MGAP4D
