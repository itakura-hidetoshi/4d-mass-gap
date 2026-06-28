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
  apply (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp
  apply Measurable.prodMk
  · exact measurable_fst
  · exact measurable_snd.fst

/-- The newly assembled configuration is measurable in old value, off-link
configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkAssemble_new
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.base.singleLinkAssemble target z.2.2 z.2.1) := by
  apply (measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp
  apply Measurable.prodMk
  · exact measurable_snd.snd
  · exact measurable_snd.fst

/-- The compact one-link joint transition density is jointly measurable in old
value, off-link configuration, and new value. -/
theorem measurable_compact_oriented_singleLinkJointDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkJointDensity target z.1 z.2.2 z.2.1) := by
  have hOld := measurable_compact_oriented_singleLinkAssemble_old C target
  have hGlobal : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkCoordinateGibbsDensity target (z.1, z.2.1)) := by
    apply
      (continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
        C target).comp
    apply Measurable.prodMk
    · exact measurable_fst
    · exact measurable_snd.fst
  have hBoltzmann : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkBoltzmannFactor
          (C.base.singleLinkAssemble target z.1 z.2.1) target z.2.2) := by
    apply
      (continuous_compact_oriented_singleLinkBoltzmannFactor_uncurry
        C target).measurable.comp
    apply Measurable.prodMk
    · exact hOld
    · exact measurable_snd.snd
  have hPartition : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkPartitionFunction
          (C.base.singleLinkAssemble target z.1 z.2.1) target) :=
    (measurable_compact_oriented_singleLinkPartitionFunction C target).comp hOld
  have hConditional : Measurable (fun z : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) =>
        C.singleLinkConditionalDensity target
          (C.base.singleLinkAssemble target z.1 z.2.1) z.2.2) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    exact ENNReal.measurable_ofReal.comp (hBoltzmann.div hPartition)
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
  apply hPhi.comp
  apply Measurable.prodMk
  · exact measurable_compact_oriented_singleLinkAssemble_old C target
  · exact measurable_compact_oriented_singleLinkAssemble_new C target

end

end MathlibAnalytic
end MGAP4D
