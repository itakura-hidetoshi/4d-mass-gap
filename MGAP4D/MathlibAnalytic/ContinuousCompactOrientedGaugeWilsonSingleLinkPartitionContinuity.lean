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
  have hMeas : ∀ A : C.base.Configuration,
      AEStronglyMeasurable (fun g : C.base.Gauge => F (A, g))
        (normalizedCompactHaar C.base.Gauge) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound : ∀ A : C.base.Configuration,
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => hNorm A g
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

end
end MathlibAnalytic
end MGAP4D
