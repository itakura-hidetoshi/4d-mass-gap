import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathStationarityCore
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionMeasurable
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory ProbabilityTheory
noncomputable section

theorem continuous_compact_oriented_integrable_of_uniform_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : StronglyMeasurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  refine Integrable.mono' (integrable_const M) hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa [Real.norm_eq_abs] using hM x

theorem continuous_compact_oriented_integral_singleLinkHeatBathKernel_eq_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) (hf : StronglyMeasurable f) (A : C.base.Configuration) :
    ∫ B, f B ∂C.singleLinkHeatBathKernel target A = C.singleLinkHeatBathProjection target f A := by
  rw [continuous_compact_oriented_singleLinkHeatBathKernel_apply]
  rw [MeasureTheory.integral_map
    (continuous_compact_oriented_replaceLink C A target).measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

theorem continuous_compact_oriented_integrable_joint_of_uniform_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ)
    (hPhi : StronglyMeasurable Phi) (M : ℝ) (hM : ∀ z, |Phi z| ≤ M) :
    Integrable Phi (C.singleLinkHeatBathJointMeasure target) :=
  continuous_compact_oriented_integrable_of_uniform_bound
    (C.singleLinkHeatBathJointMeasure target) Phi hPhi M hM

theorem continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ)
    (hPhi : Integrable Phi (C.singleLinkHeatBathJointMeasure target)) :
    ∫ z, Phi z ∂C.singleLinkHeatBathJointMeasure target =
      ∫ A, ∫ B, Phi (A, B) ∂C.singleLinkHeatBathKernel target A ∂C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
  exact Measure.integral_compProd hPhi

end
end MathlibAnalytic
end MGAP4D
