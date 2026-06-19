import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Function

noncomputable section

/-- Each physical positive-link coordinate map induced by a vertex gauge
transformation preserves normalized Haar probability measure. -/
theorem compact_oriented_link_measurePreserving
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (e : L.geometry.Edge) :
    MeasurePreserving
      (fun x : L.Gauge =>
        gamma (L.geometry.edgeSource e) * x *
          (gamma (L.geometry.edgeTarget e))⁻¹)
      (normalizedCompactHaar L.Gauge)
      (normalizedCompactHaar L.Gauge) :=
  normalizedCompactHaar_measurePreserving_mul_left_right
    L.Gauge
    (gamma (L.geometry.edgeSource e))
    (gamma (L.geometry.edgeTarget e))⁻¹

/-- A vertex gauge transformation preserves product Haar measure on physical
positive-link configurations. -/
theorem compact_oriented_configurationHaar_measurePreserving
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation) :
    MeasurePreserving (L.gaugeTransform gamma)
      L.configurationHaarMeasure L.configurationHaarMeasure := by
  refine ⟨?_, ?_⟩
  · unfold CompactOrientedGaugeWilsonSystem.gaugeTransform
    fun_prop
  · unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
    let f : L.geometry.Edge → L.Gauge → L.Gauge := fun e x =>
      gamma (L.geometry.edgeSource e) * x *
        (gamma (L.geometry.edgeTarget e))⁻¹
    have hf : ∀ e,
        AEMeasurable (f e) (normalizedCompactHaar L.Gauge) :=
      fun e =>
        (compact_oriented_link_measurePreserving L gamma e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar L.Gauge).map (f e)) := fun e => by
      rw [(compact_oriented_link_measurePreserving L gamma e).map_eq]
      infer_instance
    rw [show L.gaugeTransform gamma = (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact (compact_oriented_link_measurePreserving L gamma e).map_eq

/-- Every finite-volume continuous compact oriented Wilson Gibbs law is
invariant under vertex gauge transformations. -/
theorem continuous_compact_oriented_gibbs_measurePreserving
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gamma : C.base.GaugeTransformation) :
    MeasurePreserving (C.base.gaugeTransform gamma)
      C.gibbsMeasure C.gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · exact compact_oriented_configurationHaar_measurePreserving C.base gamma
  · exact (continuous_compact_oriented_gibbsExponent C).measurable
  · exact compact_oriented_gibbsExponent_gaugeInvariant C.base gamma
  · exact continuous_compact_oriented_boltzmannIntegrable C

/-- Pushforward formulation of finite-volume gauge invariance. -/
theorem continuous_compact_oriented_gibbs_map_eq_self
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gamma : C.base.GaugeTransformation) :
    Measure.map (C.base.gaugeTransform gamma) C.gibbsMeasure =
      C.gibbsMeasure :=
  (continuous_compact_oriented_gibbs_measurePreserving C gamma).map_eq

/-- Gauge invariance of every measurable finite-volume event. -/
theorem continuous_compact_oriented_gibbs_preimage_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gamma : C.base.GaugeTransformation)
    {s : Set C.base.Configuration}
    (hs : MeasurableSet s) :
    C.gibbsMeasure ((C.base.gaugeTransform gamma) ⁻¹' s) =
      C.gibbsMeasure s := by
  have hMP := continuous_compact_oriented_gibbs_measurePreserving C gamma
  calc
    C.gibbsMeasure ((C.base.gaugeTransform gamma) ⁻¹' s) =
        Measure.map (C.base.gaugeTransform gamma) C.gibbsMeasure s := by
          rw [Measure.map_apply hMP.measurable hs]
    _ = C.gibbsMeasure s := by rw [hMP.map_eq]

end

end MathlibAnalytic
end MGAP4D
