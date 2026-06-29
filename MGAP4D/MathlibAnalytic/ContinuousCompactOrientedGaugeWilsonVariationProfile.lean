import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinMatrix
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanNormContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proof-relevant physical-link oscillation bound for a bounded continuous
compact oriented Wilson observable. -/
structure ContinuousCompactOrientedGaugeWilsonLinkVariationBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) where
  variation : C.base.geometry.Edge → ℝ
  variation_nonneg : ∀ e : C.base.geometry.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : C.base.geometry.Edge) (A B : C.base.Configuration),
      C.base.AgreeOffLink A B e → |O A - O B| ≤ variation e

/-- A compact physical-link oscillation profile equipped with a center on each
one-link fiber. -/
structure ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    extends ContinuousCompactOrientedGaugeWilsonLinkVariationBound C O where
  fiberCenter : C.base.Configuration → C.base.geometry.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : C.base.Configuration) (e : C.base.geometry.Edge) (g : C.base.Gauge),
      |O (C.base.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

/-- A common target replacement preserves agreement away from a separately
specified compact physical source link. -/
theorem compact_oriented_replaceLink_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    L.AgreeOffLink
      (L.replaceLink A target g)
      (L.replaceLink B target g)
      source := by
  intro e he
  by_cases ht : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, ht, hAgree e he]

/-- Linkwise variation after one exact compact target-link update. -/
noncomputable def continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (target source : C.base.geometry.Edge) : ℝ := by
  classical
  exact if source = target then 0
    else variation source + D.influence target source * variation target

/-- The compact updated variation profile is nonnegative. -/
theorem continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (target source : C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
      D variation target source := by
  classical
  unfold continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

end
end MathlibAnalytic
end MGAP4D
