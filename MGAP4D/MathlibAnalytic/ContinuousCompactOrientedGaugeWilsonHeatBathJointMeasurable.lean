import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonTripleHaarSwap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Assembly is jointly measurable in the selected-link value and off-link
configuration. -/
theorem measurable_compact_oriented_singleLinkAssemble_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      C.base.OffLinkConfiguration target =>
        C.base.singleLinkAssemble target z.1 z.2) :=
  (C.base.singleLinkCoordinatesMeasurableEquiv target).symm.measurable

/-- The old assembled configuration is measurable in old value, off-link
configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkAssemble_old
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.base.singleLinkAssemble target z.1 z.2.1) := by
  have hOldCoordinates : Measurable
      (fun z : C.base.Gauge ×
        (C.base.OffLinkConfiguration target × C.base.Gauge) =>
          (z.1, z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  exact
    (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp
      hOldCoordinates

/-- The newly assembled configuration is measurable in old value, off-link
configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkAssemble_new
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.base.singleLinkAssemble target z.2.2 z.2.1) := by
  have hNewCoordinates : Measurable
      (fun z : C.base.Gauge ×
        (C.base.OffLinkConfiguration target × C.base.Gauge) =>
          (z.2.2, z.2.1)) :=
    measurable_snd.snd.prodMk measurable_snd.fst
  exact
    (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp
      hNewCoordinates

/-- The compact one-link joint transition density is jointly measurable in old
value, off-link configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkJointDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkJointDensity target z.1 z.2.2 z.2.1) := by
  have hOldCoordinates : Measurable
      (fun z : C.base.Gauge ×
        (C.base.OffLinkConfiguration target × C.base.Gauge) =>
          (z.1, z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hGlobal : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkCoordinateGibbsDensity target (z.1, z.2.1)) :=
    (continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
      C target).comp hOldCoordinates
  have hConditionalCoordinates : Measurable
      (fun z : C.base.Gauge ×
        (C.base.OffLinkConfiguration target × C.base.Gauge) =>
          (C.base.singleLinkAssemble target z.1 z.2.1, z.2.2)) :=
    (measurable_compact_oriented_singleLinkAssemble_old C target).prodMk
      measurable_snd.snd
  have hConditional : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkConditionalDensity target
          (C.base.singleLinkAssemble target z.1 z.2.1) z.2.2) :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp hConditionalCoordinates
  exact hGlobal.mul hConditional

/-- Any measurable transition observable evaluated on the old and newly
assembled configurations remains jointly measurable. -/
theorem measurable_compact_oriented_transitionObservable_assembled
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        Phi
          (C.base.singleLinkAssemble target z.1 z.2.1,
            C.base.singleLinkAssemble target z.2.2 z.2.1)) := by
  have hAssembledPair : Measurable
      (fun z : C.base.Gauge ×
        (C.base.OffLinkConfiguration target × C.base.Gauge) =>
          (C.base.singleLinkAssemble target z.1 z.2.1,
            C.base.singleLinkAssemble target z.2.2 z.2.1)) :=
    (measurable_compact_oriented_singleLinkAssemble_old C target).prodMk
      (measurable_compact_oriented_singleLinkAssemble_new C target)
  exact hPhi.comp hAssembledPair

end

end MathlibAnalytic
end MGAP4D
