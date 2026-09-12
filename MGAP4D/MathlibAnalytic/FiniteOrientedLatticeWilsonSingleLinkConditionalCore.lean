import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinLocalExpectationComparison
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonVariationProfile
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact one-link conditional average of a real observable under the oriented
Wilson conditional law. The distinct name avoids changing the established
single-link conditional probability core. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalAverage
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A target g).toReal *
      f (L.replaceLink A target g)

/-- A common centered test function is controlled by twice the oriented
conditional total variation times its fiber radius. -/
theorem finite_oriented_conditionalAverage_common_test_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (h : L.Gauge → ℝ)
    (center radius : ℝ)
    (hRadius : ∀ g : L.Gauge, |h g - center| ≤ radius) :
    |(∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal * h g) -
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF B target g).toReal * h g| ≤
      2 * L.singleLinkConditionalTotalVariation A B target * radius := by
  calc
    |(∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal * h g) -
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF B target g).toReal * h g| ≤
      (∑ g : L.Gauge,
        |(L.singleLinkConditionalPMF A target g).toReal -
          (L.singleLinkConditionalPMF B target g).toReal|) * radius :=
      finite_pmf_expectation_difference_abs_le_two_mul_tv_mul_radius
        (L.singleLinkConditionalPMF A target)
        (L.singleLinkConditionalPMF B target)
        h center radius hRadius
    _ = 2 * L.singleLinkConditionalTotalVariation A B target * radius := by
      unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
      ring

/-- Applying the same target replacement preserves agreement away from a
separately declared source link. -/
theorem finite_oriented_replaceLink_agreeOffLink_forConditionalAverage
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
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink,
      ht, hAgree e he]

/-- Replacing the target link erases every difference confined to that target
link. -/
theorem finite_oriented_replaceLink_eq_forConditionalAverage
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B target) :
    L.replaceLink A target g = L.replaceLink B target g := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink,
      h, hAgree e h]

/-- The established oriented conditional PMF is constant on off-target
configuration fibers. -/
theorem finite_oriented_conditionalPMF_eq_forConditionalAverage
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalPMF A target =
      L.singleLinkConditionalPMF B target := by
  have hWeight : ∀ g : L.Gauge,
      L.singleLinkBoltzmannWeight A target g =
        L.singleLinkBoltzmannWeight B target g := by
    intro g
    unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    rw [finite_oriented_replaceLink_eq_forConditionalAverage
      L A B target g hAgree]
  have hPartition :
      L.singleLinkPartitionFunction A target =
        L.singleLinkPartitionFunction B target := by
    unfold FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
    congr 1
    funext g
    exact hWeight g
  ext g
  rw [finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkConditionalPMF_apply,
    hWeight g, hPartition]

/-- The one-link conditional average is constant on each off-target fiber. -/
theorem finite_oriented_singleLinkConditionalAverage_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalAverage f A target =
      L.singleLinkConditionalAverage f B target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalAverage
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_conditionalPMF_eq_forConditionalAverage
      L A B target hAgree,
    finite_oriented_replaceLink_eq_forConditionalAverage
      L A B target g hAgree]

/-- A Dobrushin matrix transports a centered variation profile through one exact
conditional average. The direct source variation and transported target
variation remain separated. -/
theorem finite_oriented_dobrushin_centeredProfile_conditionalAverage_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.singleLinkConditionalAverage f A target -
        L.singleLinkConditionalAverage f B target| ≤
      P.variation source +
        D.influence target source * P.variation target := by
  classical
  let pA := L.singleLinkConditionalPMF A target
  let pB := L.singleLinkConditionalPMF B target
  let hA : L.Gauge → ℝ := fun g => f (L.replaceLink A target g)
  let hB : L.Gauge → ℝ := fun g => f (L.replaceLink B target g)
  have hDirect :
      |∑ g : L.Gauge, (pA g).toReal * (hA g - hB g)| ≤
        P.variation source := by
    apply finite_pmf_abs_expectation_le_bound
    intro g
    exact P.variation_bound source
      (L.replaceLink A target g)
      (L.replaceLink B target g)
      (finite_oriented_replaceLink_agreeOffLink_forConditionalAverage
        L A B target source g hAgree)
  have hLaw :
      |(∑ g : L.Gauge, (pA g).toReal * hB g) -
        ∑ g : L.Gauge, (pB g).toReal * hB g| ≤
        D.influence target source * P.variation target := by
    have hTV := D.conditionalTotalVariation_le
      target source A B hAgree
    calc
      |(∑ g : L.Gauge, (pA g).toReal * hB g) -
        ∑ g : L.Gauge, (pB g).toReal * hB g| ≤
          2 * L.singleLinkConditionalTotalVariation A B target *
            (P.variation target / 2) := by
        exact finite_oriented_conditionalAverage_common_test_abs_le
          L A B target hB (P.fiberCenter B target)
          (P.variation target / 2)
          (by
            intro g
            exact P.fiber_radius_bound B target g)
      _ ≤ 2 * D.influence target source *
            (P.variation target / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTV (by norm_num))
          (div_nonneg (P.variation_nonneg target) (by norm_num))
      _ = D.influence target source * P.variation target := by ring
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalAverage
  change
    |(∑ g : L.Gauge, (pA g).toReal * hA g) -
      ∑ g : L.Gauge, (pB g).toReal * hB g| ≤ _
  have hSplit :
      (∑ g : L.Gauge, (pA g).toReal * hA g) -
          ∑ g : L.Gauge, (pB g).toReal * hB g =
        (∑ g : L.Gauge, (pA g).toReal * (hA g - hB g)) +
          ((∑ g : L.Gauge, (pA g).toReal * hB g) -
            ∑ g : L.Gauge, (pB g).toReal * hB g) := by
    have hFirst :
        (∑ g : L.Gauge, (pA g).toReal * hA g) -
            ∑ g : L.Gauge, (pA g).toReal * hB g =
          ∑ g : L.Gauge, (pA g).toReal * (hA g - hB g) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    calc
      (∑ g : L.Gauge, (pA g).toReal * hA g) -
          ∑ g : L.Gauge, (pB g).toReal * hB g =
        ((∑ g : L.Gauge, (pA g).toReal * hA g) -
          ∑ g : L.Gauge, (pA g).toReal * hB g) +
          ((∑ g : L.Gauge, (pA g).toReal * hB g) -
            ∑ g : L.Gauge, (pB g).toReal * hB g) := by ring
      _ = _ := by rw [hFirst]
  rw [hSplit]
  exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

/-- Linkwise variation after one exact target-link conditional average. The
updated target has zero variation; every other source retains its direct
variation plus transported target influence. -/
noncomputable def finiteOrientedConditionalAverageUpdatedVariation
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target source : L.Edge) : ℝ := by
  classical
  exact if source = target then 0
    else variation source + D.influence target source * variation target

/-- The updated variation is nonnegative whenever the original profile is
nonnegative. -/
theorem finiteOrientedConditionalAverageUpdatedVariation_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target source : L.Edge) :
    0 ≤ finiteOrientedConditionalAverageUpdatedVariation
      D variation target source := by
  classical
  unfold finiteOrientedConditionalAverageUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

/-- Package the one-link Dobrushin update as a proof-relevant variation bound
for the conditional-average observable. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.conditionalAverageVariationBound
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    FiniteOrientedLatticeWilsonLinkVariationBound L
      (fun A => L.singleLinkConditionalAverage f A target) := by
  classical
  refine
    { variation := finiteOrientedConditionalAverageUpdatedVariation
        D P.variation target
      variation_nonneg :=
        finiteOrientedConditionalAverageUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A B hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      finite_oriented_singleLinkConditionalAverage_eq_of_agreeOffLink
        L f A B target hAgree
    rw [hEq]
    simp [finiteOrientedConditionalAverageUpdatedVariation]
  · simpa [finiteOrientedConditionalAverageUpdatedVariation, h] using
      (finite_oriented_dobrushin_centeredProfile_conditionalAverage_abs_le
        L D f P target source A B hAgree)

end

end MathlibAnalytic
end MGAP4D
