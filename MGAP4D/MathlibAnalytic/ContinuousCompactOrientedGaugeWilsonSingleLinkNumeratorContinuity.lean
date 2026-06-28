import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkPartitionContinuity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Unnormalized one-link Boltzmann numerator for a bounded continuous compact
Wilson observable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    Real.exp (C.singleLinkGibbsExponent A target g) *
      O (C.base.replaceLink A target g)
    ∂normalizedCompactHaar C.base.Gauge

/-- The Boltzmann-weighted observable integrand is jointly continuous in the
ambient compact configuration and inserted link value. -/
theorem continuous_compact_oriented_singleLinkBoltzmannObservable_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        Real.exp (C.singleLinkGibbsExponent z.1 target z.2) *
          O (C.base.replaceLink z.1 target z.2)) :=
  (continuous_compact_oriented_singleLinkBoltzmann_prod C target).mul
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink_prod C target))

/-- The unnormalized one-link Boltzmann numerator varies continuously with the
ambient compact configuration. -/
theorem continuous_compact_oriented_singleLinkBoltzmannNumerator_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkBoltzmannNumerator O A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z => Real.exp (C.singleLinkGibbsExponent z.1 target z.2) *
      O (C.base.replaceLink z.1 target z.2)
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkBoltzmannObservable_prod
        C O target
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
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

end
end MathlibAnalytic
end MGAP4D
