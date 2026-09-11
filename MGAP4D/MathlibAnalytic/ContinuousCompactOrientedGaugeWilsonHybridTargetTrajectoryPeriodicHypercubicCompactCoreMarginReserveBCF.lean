import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicMetricBallNeighborhoodBCF
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicCompactCoreAmbientMatrixPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

local instance periodicCompactCoreEndpointSystemGaugePseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  change TopologicalSpace.PseudoMetrizableSpace
    {U : Matrix (Fin 2) (Fin 2) ℂ |
      U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ}
  infer_instance

local instance periodicCompactCoreEndpointPairPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) := by
  infer_instance

local instance periodicCompactCoreEndpointPairPseudoMetricSpace :
    PseudoMetricSpace
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric _

/-- Shrinking the positive-radius ball from the previous layer by a factor two
produces a compact closed ball still contained in the threshold-six neighborhood. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_subset_explicitMarginLowerBoundNeighborhoodBCF :
    ∃ ε : ℝ,
      0 < ε ∧
      IsCompact (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_metricBall_subset with
    ⟨r, hr, hBall⟩
  refine ⟨r / 2, by linarith, Metric.isClosed_closedBall.isCompact, ?_⟩
  intro z hz
  apply hBall
  rw [Metric.mem_ball]
  rw [Metric.mem_closedBall] at hz
  linarith

/-- Compactness upgrades the pointwise strict threshold-six inequality on the
closed core to one uniform positive reserve `η` above six. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_uniform_margin_reserve :
    ∃ ε η : ℝ,
      0 < ε ∧
      0 < η ∧
      IsCompact (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ∧
      ∀ z ∈ Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε,
        (6 : ℝ) + η ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_subset_explicitMarginLowerBoundNeighborhoodBCF with
    ⟨ε, hε, hCompact, hSubset⟩
  have hContinuous :
      Continuous
        (fun z :
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z) :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_continuous
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
  have hStrict :
      ∀ z ∈ Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε,
        (6 : ℝ) <
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
    intro z hz
    exact
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_margin_gt_six
        (hSubset hz)
  rcases hCompact.exists_forall_le' hContinuous.continuousOn hStrict with
    ⟨m, hm, hLower⟩
  refine ⟨ε, m - 6, hε, sub_pos.mpr hm, hCompact, hSubset, ?_⟩
  intro z hz
  have hzLower := hLower z hz
  linarith

/-- The compact closed core has strictly positive configuration Haar-pair and
independent Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_measure_pos :
    ∃ ε : ℝ,
      0 < ε ∧
      IsCompact (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ∧
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_subset_explicitMarginLowerBoundNeighborhoodBCF with
    ⟨ε, hε, hCompact, hSubset⟩
  have hBallNonempty :
      (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε).Nonempty :=
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair, Metric.mem_ball_self hε⟩
  have hHaarBall :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
      hBallNonempty
  have hGibbsBall :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hBallNonempty
  have hHaarClosed :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    lt_of_lt_of_le hHaarBall (measure_mono Metric.ball_subset_closedBall)
  have hGibbsClosed :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    lt_of_lt_of_le hGibbsBall (measure_mono Metric.ball_subset_closedBall)
  exact ⟨ε, hε, hCompact, hSubset, hHaarClosed, hGibbsClosed⟩

/-- The actual threshold-six neighborhood therefore contains a compact positive-mass
core carrying both a uniform positive margin reserve and a strictly positive
Haar-relative lower bound beneath its Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_uniform_margin_and_mass_lowerBound :
    ∃ ε η c : ℝ,
      0 < ε ∧
      0 < η ∧
      0 < c ∧
      IsCompact (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ∧
      (∀ z ∈ Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε,
        (6 : ℝ) + η ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z) ∧
      0 <
        ((ENNReal.ofReal c * ENNReal.ofReal c) •
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      ((ENNReal.ofReal c * ENNReal.ofReal c) •
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ≤
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_uniform_margin_reserve with
    ⟨ε, η, hε, hη, hCompact, hSubset, hMargin⟩
  rcases
      continuous_compact_oriented_exists_gibbsMeasure_prod_haarMeasure_prod_lowerBoundBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem with
    ⟨c, hc, hDom⟩
  have hBallNonempty :
      (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε).Nonempty :=
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair, Metric.mem_ball_self hε⟩
  have hHaarBall :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
      hBallNonempty
  have hHaarClosed :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    lt_of_lt_of_le hHaarBall (measure_mono Metric.ball_subset_closedBall)
  have hDensitySquare : 0 < ENNReal.ofReal c * ENNReal.ofReal c :=
    ENNReal.mul_pos
      (ne_of_gt (ENNReal.ofReal_pos.2 hc))
      (ne_of_gt (ENNReal.ofReal_pos.2 hc))
  have hProduct :
      0 <
        (ENNReal.ofReal c * ENNReal.ofReal c) *
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
            (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    ENNReal.mul_pos (ne_of_gt hDensitySquare) (ne_of_gt hHaarClosed)
  have hScaled :
      0 <
        ((ENNReal.ofReal c * ENNReal.ofReal c) •
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
    simpa [Measure.smul_apply] using hProduct
  exact
    ⟨ε, η, c, hε, hη, hc, hCompact, hSubset, hMargin, hScaled,
      hDom (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε)⟩

end

end MathlibAnalytic
end MGAP4D
