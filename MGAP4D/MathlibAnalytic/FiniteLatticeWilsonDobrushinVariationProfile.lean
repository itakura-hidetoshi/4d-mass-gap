import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinLocalExpectationComparison
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure FiniteLatticeWilsonLinkVariationBound
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) where
  variation : L.Edge → ℝ
  variation_nonneg : ∀ e : L.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : L.Edge) (A B : L.Configuration),
      L.AgreeOffLink A B e → |f A - f B| ≤ variation e

structure FiniteLatticeWilsonCenteredVariationProfile
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    extends FiniteLatticeWilsonLinkVariationBound L f where
  fiberCenter : L.Configuration → L.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : L.Configuration) (e : L.Edge) (g : L.Gauge),
      |f (L.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

theorem finite_lattice_replaceLink_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
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
  · simp [FiniteLatticeWilsonSystem.replaceLink, ht, hAgree e he]

theorem finite_lattice_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (f : L.Configuration → ℝ)
    (P : FiniteLatticeWilsonCenteredVariationProfile L f)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.singleLinkConditionalExpectation f A target -
        L.singleLinkConditionalExpectation f B target| ≤
      P.variation source +
        D.influence target source * P.variation target := by
  have hSourceBound :
      ∀ g : L.Gauge,
        |f (L.replaceLink A target g) -
          f (L.replaceLink B target g)| ≤ P.variation source := by
    intro g
    exact P.variation_bound source
      (L.replaceLink A target g)
      (L.replaceLink B target g)
      (finite_lattice_replaceLink_agreeOffLink
        L A B target source g hAgree)
  have hRadiusNonneg : 0 ≤ P.variation target / 2 :=
    div_nonneg (P.variation_nonneg target) (by norm_num)
  calc
    |L.singleLinkConditionalExpectation f A target -
        L.singleLinkConditionalExpectation f B target| ≤
      P.variation source +
        2 * D.influence target source * (P.variation target / 2) :=
      finite_lattice_dobrushin_singleLinkConditionalExpectation_difference_abs_le
        L D target source A B hAgree f
        (P.variation source) (P.variation target / 2)
        (P.fiberCenter B target)
        hSourceBound hRadiusNonneg
        (P.fiber_radius_bound B target)
    _ = P.variation source +
        D.influence target source * P.variation target := by
      ring

def finiteLatticeWilsonDobrushinUpdatedVariation
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target source : L.Edge) : ℝ :=
  if source = target then 0
  else variation source + D.influence target source * variation target

theorem finite_lattice_dobrushinUpdatedVariation_nonneg
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target source : L.Edge) :
    0 ≤ finiteLatticeWilsonDobrushinUpdatedVariation
      D variation target source := by
  classical
  unfold finiteLatticeWilsonDobrushinUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

noncomputable def
    FiniteLatticeWilsonCenteredVariationProfile.conditionalExpectationVariationBound
    {L : FiniteLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    FiniteLatticeWilsonLinkVariationBound L
      (fun A => L.singleLinkConditionalExpectation f A target) := by
  classical
  refine
    { variation := finiteLatticeWilsonDobrushinUpdatedVariation
        D P.variation target
      variation_nonneg :=
        finite_lattice_dobrushinUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A B hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
        L f A B target hAgree
    rw [hEq]
    simp [finiteLatticeWilsonDobrushinUpdatedVariation]
  · simpa [finiteLatticeWilsonDobrushinUpdatedVariation, h] using
      (finite_lattice_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
        L D f P target source A B hAgree)

end

end MathlibAnalytic
end MGAP4D
