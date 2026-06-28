import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinLocalExpectationComparison

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proof-relevant physical-link oscillation bound for an orientation-correct
finite Wilson observable. -/
structure FiniteOrientedLatticeWilsonLinkVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) where
  variation : L.Edge → ℝ
  variation_nonneg : ∀ e : L.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : L.Edge) (A B : L.Configuration),
      L.AgreeOffLink A B e → |f A - f B| ≤ variation e

/-- A physical-link oscillation profile with a center on every one-link fiber.
The half-variation radius gives the sharp total-variation normalization. -/
structure FiniteOrientedLatticeWilsonCenteredVariationProfile
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    extends FiniteOrientedLatticeWilsonLinkVariationBound L f where
  fiberCenter : L.Configuration → L.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : L.Configuration) (e : L.Edge) (g : L.Gauge),
      |f (L.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

/-- Applying the same target replacement preserves agreement away from a
separately declared physical source link. -/
theorem finite_oriented_replaceLink_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
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
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, ht, hAgree e he]

/-- A centered fiber profile converts the local total-variation estimate into
the sharp orientation-correct Dobrushin variation update. -/
theorem finite_oriented_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
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
      (finite_oriented_replaceLink_agreeOffLink
        L A B target source g hAgree)
  have hRadiusNonneg : 0 ≤ P.variation target / 2 :=
    div_nonneg (P.variation_nonneg target) (by norm_num)
  calc
    |L.singleLinkConditionalExpectation f A target -
        L.singleLinkConditionalExpectation f B target| ≤
      P.variation source +
        2 * D.influence target source * (P.variation target / 2) :=
      finite_oriented_dobrushin_singleLinkConditionalExpectation_difference_abs_le
        L D target source A B hAgree f
        (P.variation source) (P.variation target / 2)
        (P.fiberCenter B target)
        hSourceBound hRadiusNonneg
        (P.fiber_radius_bound B target)
    _ = P.variation source +
        D.influence target source * P.variation target := by ring

/-- Linkwise variation after one exact oriented target-link update.  The
updated link has zero variation, while every other source retains its direct
variation plus transported target influence. -/
noncomputable def finiteOrientedLatticeWilsonDobrushinUpdatedVariation
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target source : L.Edge) : ℝ := by
  classical
  exact if source = target then 0
    else variation source + D.influence target source * variation target

/-- The oriented updated variation profile is nonnegative. -/
theorem finite_oriented_dobrushinUpdatedVariation_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target source : L.Edge) :
    0 ≤ finiteOrientedLatticeWilsonDobrushinUpdatedVariation
      D variation target source := by
  classical
  unfold finiteOrientedLatticeWilsonDobrushinUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

/-- Package the sharp one-link update as a physical-link variation bound for
the exact oriented conditional expectation observable. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.conditionalExpectationVariationBound
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    FiniteOrientedLatticeWilsonLinkVariationBound L
      (fun A => L.singleLinkConditionalExpectation f A target) := by
  classical
  refine
    { variation := finiteOrientedLatticeWilsonDobrushinUpdatedVariation
        D P.variation target
      variation_nonneg :=
        finite_oriented_dobrushinUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A B hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
        L f A B target hAgree
    rw [hEq]
    simp [finiteOrientedLatticeWilsonDobrushinUpdatedVariation]
  · simpa [finiteOrientedLatticeWilsonDobrushinUpdatedVariation, h] using
      (finite_oriented_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
        L D f P target source A B hAgree)

end

end MathlibAnalytic
end MGAP4D
