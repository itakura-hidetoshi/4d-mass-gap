import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Exchange of old and newly sampled configurations is measure preserving for
the exact compact-group heat-bath joint law. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointSwapMeasurePreserving
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    MeasurePreserving Prod.swap
      (C.singleLinkHeatBathJointMeasure target)
      (C.singleLinkHeatBathJointMeasure target) :=
  ⟨measurable_swap,
    continuous_compact_oriented_map_swap_singleLinkHeatBathJointMeasure
      C target⟩

/-- Bochner integration against the compact one-link heat-bath joint law is
symmetric under exchange of old and newly sampled configurations. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Phi : C.base.Configuration × C.base.Configuration → E)
    (hPhi : AEStronglyMeasurable Phi
      (C.singleLinkHeatBathJointMeasure target)) :
    ∫ z, Phi z ∂C.singleLinkHeatBathJointMeasure target =
      ∫ z, Phi z.swap ∂C.singleLinkHeatBathJointMeasure target := by
  let J := C.singleLinkHeatBathJointMeasure target
  have hMap : Measure.map Prod.swap J = J :=
    continuous_compact_oriented_map_swap_singleLinkHeatBathJointMeasure
      C target
  have hPhiMap : AEStronglyMeasurable Phi (Measure.map Prod.swap J) := by
    simpa [hMap] using hPhi
  calc
    ∫ z, Phi z ∂J = ∫ z, Phi z ∂Measure.map Prod.swap J := by
      rw [hMap]
    _ = ∫ z, Phi z.swap ∂J :=
      MeasureTheory.integral_map measurable_swap.aemeasurable hPhiMap

end

end MathlibAnalytic
end MGAP4D
