import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLinkAssembly
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsPushforward

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Wilson Gibbs density in selected-link/off-link coordinates. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkCoordinateGibbsDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Gauge × C.base.OffLinkConfiguration target → ℝ≥0∞ :=
  fun z => ENNReal.ofReal
    (Real.exp
        (C.base.gibbsExponent
          ((C.base.singleLinkCoordinatesMeasurableEquiv target).symm z)) /
      C.base.partitionFunction)

/-- The selected-link/off-link Wilson Gibbs density is measurable. -/
theorem continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.singleLinkCoordinateGibbsDensity target) := by
  have hWeight : Measurable (fun A : C.base.Configuration =>
      Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) :=
    (continuous_compact_oriented_boltzmannFactor C).measurable.div
      measurable_const
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkCoordinateGibbsDensity
  exact ENNReal.measurable_ofReal.comp
    (hWeight.comp
      (C.base.singleLinkCoordinatesMeasurableEquiv target).symm.measurable)

/-- Exact pushforward of physical-link product Haar measure under the direct
single-link coordinate map. -/
theorem compact_oriented_map_singleLinkCoordinates_configurationHaarMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    Measure.map (L.singleLinkCoordinatesMeasurableEquiv target)
        L.configurationHaarMeasure =
      (normalizedCompactHaar L.Gauge).prod
        (L.offLinkHaarMeasure target) := by
  rw [← compact_oriented_canonicalSingleLinkCoordinates_eq_direct]
  exact
    compact_oriented_map_canonicalSingleLinkCoordinates_configurationHaarMeasure
      L target

/-- Exact pushforward of the compact oriented Wilson Gibbs law to
selected-link/off-link coordinates. -/
theorem continuous_compact_oriented_map_singleLinkCoordinates_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map (C.base.singleLinkCoordinatesMeasurableEquiv target)
        C.gibbsMeasure =
      ((normalizedCompactHaar C.base.Gauge).prod
        (C.base.offLinkHaarMeasure target)).withDensity
          (C.singleLinkCoordinateGibbsDensity target) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [compact_oriented_gibbsMeasure_eq_withDensity]
  rw [MeasurableEquiv.map_withDensity_comp_symm_transport]
  · rw [compact_oriented_map_singleLinkCoordinates_configurationHaarMeasure]
    rfl
  · exact ENNReal.measurable_ofReal.comp
      ((continuous_compact_oriented_boltzmannFactor C).measurable.div
        measurable_const)

/-- Coordinate Gibbs density evaluated at an assembled configuration. -/
theorem continuous_compact_oriented_singleLinkCoordinateGibbsDensity_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target) :
    C.singleLinkCoordinateGibbsDensity target (g, Aoff) =
      ENNReal.ofReal
        (C.gibbsDensityReal
          (C.base.singleLinkAssemble target g Aoff)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
