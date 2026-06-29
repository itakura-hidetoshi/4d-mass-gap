import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionLaws

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem continuous_compact_oriented_replaceLink_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.base.replaceLink z.1 target z.2) := by
  classical
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_snd : Continuous
        (fun z : C.base.Configuration × C.base.Gauge => z.2))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, h] using
      ((continuous_apply e).comp
        (continuous_fst : Continuous
          (fun z : C.base.Configuration × C.base.Gauge => z.1)))

theorem continuous_compact_oriented_singleLinkGibbsExponent_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.singleLinkGibbsExponent z.1 target z.2) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
  exact (continuous_compact_oriented_gibbsExponent C).comp
    (continuous_compact_oriented_replaceLink_prod C target)

theorem continuous_compact_oriented_singleLinkBoltzmann_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        Real.exp (C.singleLinkGibbsExponent z.1 target z.2)) :=
  Real.continuous_exp.comp
    (continuous_compact_oriented_singleLinkGibbsExponent_prod C target)

end
end MathlibAnalytic
end MGAP4D
