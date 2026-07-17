import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicExplicitMarginLowerBoundBCF
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A continuous strictly positive finite-volume Gibbs density on the compact
configuration space admits a uniform strictly positive real lower bound. -/
theorem continuous_compact_oriented_exists_gibbsDensityBCF_uniform_lowerBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : C.base.Configuration, c ≤ C.gibbsDensityBCF A := by
  rcases isCompact_univ.exists_forall_le'
      (continuous_compact_oriented_gibbsDensityBCF_continuous C).continuousOn
      (fun A _ => continuous_compact_oriented_gibbsDensityBCF_pos C A) with
    ⟨c, hc, hLower⟩
  exact ⟨c, hc, fun A => hLower A (Set.mem_univ A)⟩

/-- Consequently the canonical finite-volume Gibbs law dominates a strictly
positive scalar multiple of configuration Haar measure. -/
theorem continuous_compact_oriented_exists_gibbsMeasure_haarMeasure_lowerBoundBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ∃ c : ℝ, 0 < c ∧
      (ENNReal.ofReal c) • C.base.configurationHaarMeasure ≤ C.gibbsMeasure := by
  rcases continuous_compact_oriented_exists_gibbsDensityBCF_uniform_lowerBound C with
    ⟨c, hc, hLower⟩
  refine ⟨c, hc, ?_⟩
  rw [continuous_compact_oriented_gibbsMeasure_eq_withDensityBCF]
  have hMono :
      (fun _ : C.base.Configuration => ENNReal.ofReal c) ≤ᵐ[
        C.base.configurationHaarMeasure]
        (fun A => ENNReal.ofReal (C.gibbsDensityBCF A)) :=
    Filter.Eventually.of_forall fun A =>
      ENNReal.ofReal_le_ofReal (hLower A)
  simpa only [withDensity_const] using
    (withDensity_mono (μ := C.base.configurationHaarMeasure) hMono)

/-- The independent finite-volume Gibbs-pair law is the configuration Haar-pair
law tilted by the product of the two one-configuration Gibbs densities. -/
theorem continuous_compact_oriented_gibbsMeasure_prod_eq_withDensityBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.gibbsMeasure.prod C.gibbsMeasure =
      (C.base.configurationHaarMeasure.prod C.base.configurationHaarMeasure).withDensity
        (fun z : C.base.Configuration × C.base.Configuration =>
          ENNReal.ofReal (C.gibbsDensityBCF z.1) *
            ENNReal.ofReal (C.gibbsDensityBCF z.2)) := by
  have hf : Measurable
      (fun A : C.base.Configuration => ENNReal.ofReal (C.gibbsDensityBCF A)) :=
    (continuous_compact_oriented_gibbsDensityBCF_continuous C).measurable.ennreal_ofReal
  rw [continuous_compact_oriented_gibbsMeasure_eq_withDensityBCF]
  exact prod_withDensity hf hf

/-- Squaring the uniform density lower bound gives domination of the independent
Gibbs-pair law by a positive scalar multiple of the configuration Haar-pair law. -/
theorem continuous_compact_oriented_exists_gibbsMeasure_prod_haarMeasure_prod_lowerBoundBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ∃ c : ℝ, 0 < c ∧
      (ENNReal.ofReal c * ENNReal.ofReal c) •
          (C.base.configurationHaarMeasure.prod C.base.configurationHaarMeasure) ≤
        C.gibbsMeasure.prod C.gibbsMeasure := by
  rcases continuous_compact_oriented_exists_gibbsDensityBCF_uniform_lowerBound C with
    ⟨c, hc, hLower⟩
  refine ⟨c, hc, ?_⟩
  rw [continuous_compact_oriented_gibbsMeasure_prod_eq_withDensityBCF]
  have hMono :
      (fun _ : C.base.Configuration × C.base.Configuration =>
          ENNReal.ofReal c * ENNReal.ofReal c) ≤ᵐ[
        C.base.configurationHaarMeasure.prod C.base.configurationHaarMeasure]
        (fun z =>
          ENNReal.ofReal (C.gibbsDensityBCF z.1) *
            ENNReal.ofReal (C.gibbsDensityBCF z.2)) :=
    Filter.Eventually.of_forall fun z =>
      mul_le_mul'
        (ENNReal.ofReal_le_ofReal (hLower z.1))
        (ENNReal.ofReal_le_ofReal (hLower z.2))
  simpa only [withDensity_const] using
    (withDensity_mono
      (μ := C.base.configurationHaarMeasure.prod C.base.configurationHaarMeasure)
      hMono)

/-- The independent configuration Haar-pair law is positive on every nonempty
open pair region. -/
instance continuousCompactOriented_configurationHaarMeasure_prod_isOpenPosMeasureBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Measure.IsOpenPosMeasure
      (C.base.configurationHaarMeasure.prod C.base.configurationHaarMeasure) := by
  letI : IsProbabilityMeasure C.base.configurationHaarMeasure := by
    unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
    infer_instance
  infer_instance

/-- The explicit threshold-six neighborhood has strictly positive independent
configuration Haar-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_haarPair_measure_pos :
    0 <
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_isOpen.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure)
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_nonempty

/-- The actual threshold-six Gibbs-pair neighborhood mass is bounded below by a
strictly positive density-square multiple of its configuration Haar-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_gibbsPair_measure_ge_haarPair_lowerBound :
    ∃ c : ℝ, 0 < c ∧
      ((ENNReal.ofReal c * ENNReal.ofReal c) •
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ≤
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  rcases
      continuous_compact_oriented_exists_gibbsMeasure_prod_haarMeasure_prod_lowerBoundBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem with
    ⟨c, hc, hDom⟩
  exact
    ⟨c, hc,
      hDom periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF⟩

/-- The Haar-relative lower bound is itself strictly positive.  This is a
quantitative formula-level receipt; it does not yet evaluate the Haar-pair mass
as a numerical constant. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_positive_haar_relative_mass_lowerBound :
    ∃ c : ℝ, 0 < c ∧
      0 <
        ((ENNReal.ofReal c * ENNReal.ofReal c) •
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ∧
      ((ENNReal.ofReal c * ENNReal.ofReal c) •
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF ≤
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_gibbsPair_measure_ge_haarPair_lowerBound with
    ⟨c, hc, hLower⟩
  refine ⟨c, hc, ?_, hLower⟩
  simpa [Measure.smul_apply] using
    ENNReal.mul_pos.2
      ⟨ENNReal.mul_pos.2
          ⟨ENNReal.ofReal_pos.2 hc, ENNReal.ofReal_pos.2 hc⟩,
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_haarPair_measure_pos⟩

/-- In particular there is a named strictly positive extended-nonnegative-real
lower-bound receipt beneath the actual threshold-six Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_positive_mass_lowerBound_receipt :
    ∃ q : ℝ≥0∞, 0 < q ∧
      q ≤
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_exists_positive_haar_relative_mass_lowerBound with
    ⟨c, _, hq, hqLower⟩
  exact
    ⟨((ENNReal.ofReal c * ENNReal.ofReal c) •
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure.prod
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure))
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF,
      hq, hqLower⟩

end

end MathlibAnalytic
end MGAP4D
