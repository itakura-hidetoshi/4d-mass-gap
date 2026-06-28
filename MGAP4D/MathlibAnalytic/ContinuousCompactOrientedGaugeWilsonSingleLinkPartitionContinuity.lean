import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonJointReplacement
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

theorem continuous_compact_oriented_singleLinkPartitionFunction_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkPartitionFunction A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z => Real.exp (C.singleLinkGibbsExponent z.1 target z.2)
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkBoltzmann_prod C target
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hNorm : ∀ (A : C.base.Configuration) (g : C.base.Gauge),
      ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A g
    change ‖FB (A, g)‖ ≤ ‖FB‖
    exact FB.norm_coe_le_norm (A, g)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    (fun A =>
      (hF.comp (continuous_const.prod_mk continuous_id)).aestronglyMeasurable)
    (fun A => Filter.Eventually.of_forall fun g => hNorm A g)
    (integrable_const ‖FB‖)
    (Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prod_mk continuous_const))

end
end MathlibAnalytic
end MGAP4D
