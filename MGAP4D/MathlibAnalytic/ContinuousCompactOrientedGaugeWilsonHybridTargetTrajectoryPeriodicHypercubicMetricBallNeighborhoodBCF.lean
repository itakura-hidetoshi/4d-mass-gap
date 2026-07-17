import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicGibbsHaarMassLowerBoundBCF
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicMetricBallEndpointSystemGaugePseudoMetricSpace :
    PseudoMetricSpace periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  change PseudoMetricSpace (SpecialUnitaryMatrixGroup 2)
  infer_instance

/-- The open threshold-six margin neighborhood contains a positive-radius metric
ball around the concrete identity/far-side-center endpoint pair. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_metricBall_subset :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  exact Metric.mem_nhds_iff.mp
    (periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_isOpen.mem_nhds
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_mem_explicitMarginLowerBoundNeighborhoodBCF)

/-- On one positive-radius metric ball around the concrete endpoint pair, the
actual insertion-profile oscillation margin is uniformly strictly larger than six. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_metricBall_margin_gt_six :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε,
        (6 : ℝ) <
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_metricBall_subset with
    ⟨ε, hε, hBall⟩
  refine ⟨ε, hε, ?_⟩
  intro z hz
  exact
    periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_margin_gt_six
      (hBall hz)

/-- The positive-radius metric ball may be chosen with strictly positive Haar-pair
and independent Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_metricBall_measure_pos :
    ∃ ε : ℝ, 0 < ε ∧
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_metricBall_subset with
    ⟨ε, hε, _⟩
  have hNonempty :
      (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε).Nonempty :=
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair, Metric.mem_ball_self hε⟩
  have hHaar :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
      hNonempty
  have hGibbs :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hNonempty
  exact ⟨ε, hε, hHaar, hGibbs⟩

/-- A positive-radius metric ball inside the threshold-six neighborhood carries a
strictly positive Haar-relative quantitative lower bound beneath its Gibbs-pair
mass.  The radius and density constant are existential but positive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_metricBall_positive_haar_relative_mass_lowerBound :
    ∃ ε c : ℝ,
      0 < ε ∧
      0 < c ∧
      Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε ⊆
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ∧
      0 <
        ((ENNReal.ofReal c * ENNReal.ofReal c) •
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      ((ENNReal.ofReal c * ENNReal.ofReal c) •
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ≤
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_metricBall_subset with
    ⟨ε, hε, hBall⟩
  rcases
      continuous_compact_oriented_exists_gibbsMeasure_prod_haarMeasure_prod_lowerBoundBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem with
    ⟨c, hc, hDom⟩
  have hNonempty :
      (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε).Nonempty :=
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair, Metric.mem_ball_self hε⟩
  have hHaar :
      0 <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    Metric.isOpen_ball.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
      hNonempty
  have hDensitySquare : 0 < ENNReal.ofReal c * ENNReal.ofReal c :=
    ENNReal.mul_pos
      (ne_of_gt (ENNReal.ofReal_pos.2 hc))
      (ne_of_gt (ENNReal.ofReal_pos.2 hc))
  have hProduct :
      0 <
        (ENNReal.ofReal c * ENNReal.ofReal c) *
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
            (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) :=
    ENNReal.mul_pos (ne_of_gt hDensitySquare) (ne_of_gt hHaar)
  have hScaled :
      0 <
        ((ENNReal.ofReal c * ENNReal.ofReal c) •
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) := by
    simpa [Measure.smul_apply] using hProduct
  exact
    ⟨ε, c, hε, hc, hBall, hScaled,
      hDom (Metric.ball periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε)⟩

end

end MathlibAnalytic
end MGAP4D
