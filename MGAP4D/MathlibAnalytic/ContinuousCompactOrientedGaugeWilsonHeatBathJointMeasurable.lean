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
  have hPair : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        (z.1, z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  simpa only [Function.comp_apply] using
    (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp hPair

/-- The newly assembled configuration is measurable in old value, off-link
configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkAssemble_new
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.base.singleLinkAssemble target z.2.2 z.2.1) := by
  have hPair : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        (z.2.2, z.2.1)) :=
    measurable_snd.snd.prodMk measurable_snd.fst
  simpa only [Function.comp_apply] using
    (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp hPair

/-- The compact one-link joint transition density is jointly measurable in old
value, off-link configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkJointDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkJointDensity target z.1 z.2.2 z.2.1) := by
  have hOld := measurable_compact_oriented_singleLinkAssemble_old C target
  have hCoordinatePair : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        (z.1, z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hGlobal : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkCoordinateGibbsDensity target (z.1, z.2.1)) := by
    simpa only [Function.comp_apply] using
      (continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
        C target).comp hCoordinatePair
  have hBoltzmannPair : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        (C.base.singleLinkAssemble target z.1 z.2.1, z.2.2)) :=
    hOld.prodMk measurable_snd.snd
  have hBoltzmann : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkBoltzmannFactor
          (C.base.singleLinkAssemble target z.1 z.2.1) target z.2.2) := by
    simpa only [Function.comp_apply] using
      (continuous_compact_oriented_singleLinkBoltzmannFactor_uncurry
        C target).measurable.comp hBoltzmannPair
  have hPartition : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkPartitionFunction
          (C.base.singleLinkAssemble target z.1 z.2.1) target) := by
    simpa only [Function.comp_apply] using
      (measurable_compact_oriented_singleLinkPartitionFunction C target).comp hOld
  have hRatio : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkBoltzmannFactor
            (C.base.singleLinkAssemble target z.1 z.2.1) target z.2.2 /
          C.singleLinkPartitionFunction
            (C.base.singleLinkAssemble target z.1 z.2.1) target) :=
    hBoltzmann.div hPartition
  have hConditional : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkConditionalDensity target
          (C.base.singleLinkAssemble target z.1 z.2.1) z.2.2) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    exact ENNReal.measurable_ofReal.comp hRatio
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
  have hPair : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        (C.base.singleLinkAssemble target z.1 z.2.1,
          C.base.singleLinkAssemble target z.2.2 z.2.1)) :=
    (measurable_compact_oriented_singleLinkAssemble_old C target).prodMk
      (measurable_compact_oriented_singleLinkAssemble_new C target)
  simpa only [Function.comp_apply] using hPhi.comp hPair

end

end MathlibAnalytic
end MGAP4D
