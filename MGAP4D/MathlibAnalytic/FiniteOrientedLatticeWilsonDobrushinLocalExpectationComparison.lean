import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinLocalExpectationComparison
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditionalExpectation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For one orientation-correct Wilson conditional law, the common-test
expectation difference is controlled by twice its total variation times a
fiber radius. -/
theorem finite_oriented_singleLinkConditionalPMF_test_difference_abs_le
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

/-- An oriented Dobrushin matrix entry controls every bounded common-test
conditional expectation difference across a one-source perturbation. -/
theorem finite_oriented_dobrushin_conditionalPMF_test_difference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source)
    (h : L.Gauge → ℝ)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ g : L.Gauge, |h g - center| ≤ radius) :
    |(∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal * h g) -
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF B target g).toReal * h g| ≤
      2 * D.influence target source * radius := by
  have hTV := D.conditionalTotalVariation_le target source A B hAgree
  calc
    |(∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal * h g) -
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF B target g).toReal * h g| ≤
      2 * L.singleLinkConditionalTotalVariation A B target * radius :=
      finite_oriented_singleLinkConditionalPMF_test_difference_abs_le
        L A B target h center radius hRadius
    _ ≤ 2 * D.influence target source * radius := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTV (by norm_num)) hRadiusNonneg

/-- Local orientation-correct Dobrushin propagation for exact one-link
conditional expectations.  The direct observable change and the transported
conditional-law change remain separated. -/
theorem finite_oriented_dobrushin_singleLinkConditionalExpectation_difference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source)
    (f : L.Configuration → ℝ)
    (sourceBound targetRadius center : ℝ)
    (hSourceBound :
      ∀ g : L.Gauge,
        |f (L.replaceLink A target g) -
          f (L.replaceLink B target g)| ≤ sourceBound)
    (hTargetRadiusNonneg : 0 ≤ targetRadius)
    (hTargetRadius :
      ∀ g : L.Gauge,
        |f (L.replaceLink B target g) - center| ≤ targetRadius) :
    |L.singleLinkConditionalExpectation f A target -
        L.singleLinkConditionalExpectation f B target| ≤
      sourceBound + 2 * D.influence target source * targetRadius := by
  classical
  let pA := L.singleLinkConditionalPMF A target
  let pB := L.singleLinkConditionalPMF B target
  let hA : L.Gauge → ℝ := fun g => f (L.replaceLink A target g)
  let hB : L.Gauge → ℝ := fun g => f (L.replaceLink B target g)
  have hDirect :
      |∑ g : L.Gauge, (pA g).toReal * (hA g - hB g)| ≤ sourceBound := by
    apply finite_pmf_abs_expectation_le_bound
    intro g
    simpa [hA, hB] using hSourceBound g
  have hLaw :
      |(∑ g : L.Gauge, (pA g).toReal * hB g) -
        ∑ g : L.Gauge, (pB g).toReal * hB g| ≤
        2 * D.influence target source * targetRadius := by
    exact finite_oriented_dobrushin_conditionalPMF_test_difference_abs_le
      L D target source A B hAgree hB center targetRadius
      hTargetRadiusNonneg (by
        intro g
        simpa [hB] using hTargetRadius g)
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  change
    |(∑ g : L.Gauge, (pA g).toReal * hA g) -
        ∑ g : L.Gauge, (pB g).toReal * hB g| ≤
      sourceBound + 2 * D.influence target source * targetRadius
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
      _ = (∑ g : L.Gauge, (pA g).toReal * (hA g - hB g)) +
          ((∑ g : L.Gauge, (pA g).toReal * hB g) -
            ∑ g : L.Gauge, (pB g).toReal * hB g) := by
        rw [hFirst]
  rw [hSplit]
  exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

end

end MathlibAnalytic
end MGAP4D
