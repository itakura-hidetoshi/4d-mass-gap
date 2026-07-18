import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicCompactCoreMarginReserveBCF
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicIntegratedExcessAmbientMatrixPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

local instance periodicIntegratedExcessEndpointSystemGaugePseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  change TopologicalSpace.PseudoMetrizableSpace
    {U : Matrix (Fin 2) (Fin 2) ℂ |
      U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ}
  infer_instance

local instance periodicIntegratedExcessEndpointPairPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) := by
  infer_instance

local instance periodicIntegratedExcessEndpointPairPseudoMetricSpace :
    PseudoMetricSpace
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric _

/-- The nonnegative excess of the actual insertion-profile oscillation margin above
six, viewed as an `ℝ≥0∞`-valued function for lower Lebesgue integration. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointMarginExcessENNRealBCF
    (z :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z - 6)

/-- The Gibbs-pair lower Lebesgue integral of the threshold-six excess margin over
the compact closed ball of radius `ε` around the concrete endpoint pair. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF
    (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointMarginExcessENNRealBCF z ∂
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The compact core supplies a strictly positive quantitative lower bound for the
integrated threshold-six excess margin.  The lower bound is the uniform reserve
`η` times the already-proved Haar-relative mass bound, and it factors through the
actual Gibbs-pair mass of the core. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_integrated_excess_margin_lowerBound :
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
        ENNReal.ofReal η *
          ((ENNReal.ofReal c * ENNReal.ofReal c) •
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
            (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      ENNReal.ofReal η *
          ((ENNReal.ofReal c * ENNReal.ofReal c) •
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
            (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ≤
        ENNReal.ofReal η *
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ∧
      ENNReal.ofReal η *
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε) ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε ∧
      0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_uniform_margin_and_mass_lowerBound with
    ⟨ε, η, c, hε, hη, hc, hCompact, hSubset, hMargin, hScaledPos, hDom⟩
  let K := Metric.closedBall periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ε
  let μG :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
  let μH :=
    (ENNReal.ofReal c * ENNReal.ofReal c) •
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
  change 0 < μH K at hScaledPos
  change μH K ≤ μG K at hDom
  change ∀ z ∈ K, (6 : ℝ) + η ≤
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z at hMargin
  have hMeasurableK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hEtaENNReal : 0 < ENNReal.ofReal η := ENNReal.ofReal_pos.2 hη
  have hGibbsPos : 0 < μG K := lt_of_lt_of_le hScaledPos hDom
  have hReserveHaarPos : 0 < ENNReal.ofReal η * μH K :=
    ENNReal.mul_pos (ne_of_gt hEtaENNReal) (ne_of_gt hScaledPos)
  have hReserveGibbsPos : 0 < ENNReal.ofReal η * μG K :=
    ENNReal.mul_pos (ne_of_gt hEtaENNReal) (ne_of_gt hGibbsPos)
  have hReserveHaarLeGibbs :
      ENNReal.ofReal η * μH K ≤ ENNReal.ofReal η * μG K :=
    mul_le_mul_left' hDom (ENNReal.ofReal η)
  have hReserveGibbsLeIntegral :
      ENNReal.ofReal η * μG K ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε := by
    calc
      ENNReal.ofReal η * μG K = ∫⁻ _ in K, ENNReal.ofReal η ∂μG := by
        symm
        exact setLIntegral_const K (ENNReal.ofReal η)
      _ ≤ ∫⁻ z in K,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointMarginExcessENNRealBCF z ∂μG := by
        apply setLIntegral_mono' hMeasurableK
        intro z hz
        apply ENNReal.ofReal_le_ofReal
        dsimp [periodicHypercubicThreeSpecialUnitaryTwoEndpointMarginExcessENNRealBCF]
        have hzMargin := hMargin z hz
        linarith
      _ = periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε := by
        rfl
  have hIntegratedPos :
      0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε :=
    lt_of_lt_of_le hReserveGibbsPos hReserveGibbsLeIntegral
  exact
    ⟨ε, η, c, hε, hη, hc, hCompact, hSubset, hMargin,
      hReserveHaarPos, hReserveHaarLeGibbs, hReserveGibbsLeIntegral, hIntegratedPos⟩

/-- In particular, the actual side-three periodic `SU(2)` endpoint observable has
strictly positive Gibbs-pair integrated margin excess above the threshold six on
one compact positive-mass neighborhood. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF_pos :
    ∃ ε : ℝ,
      0 < ε ∧
      0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointIntegratedExcessMarginBCF ε := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_exists_compact_closedBall_integrated_excess_margin_lowerBound with
    ⟨ε, η, c, hε, hη, hc, hCompact, hSubset, hMargin,
      hReserveHaarPos, hReserveHaarLeGibbs, hReserveGibbsLeIntegral, hIntegratedPos⟩
  exact ⟨ε, hε, hIntegratedPos⟩

end

end MathlibAnalytic
end MGAP4D
