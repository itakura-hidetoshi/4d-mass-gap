import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The absolute value of a finite real sum is bounded by the sum of the
absolute values.  This local version keeps the Dobrushin comparison proof
independent of normed-space API details. -/
theorem finite_abs_sum_le_sum_abs
    {α : Type*} (s : Finset α) (u : α → ℝ) :
    abs (∑ a in s, u a) ≤ ∑ a in s, abs (u a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (abs_add_le _ _) (add_le_add_left ih _)

/-- A finite PMF average of a uniformly bounded real test function is bounded
by the same uniform bound. -/
theorem finite_pmf_abs_expectation_le_bound
    {α : Type*} [Fintype α]
    (p : PMF α) (h : α → ℝ) (M : ℝ)
    (hM : ∀ a : α, |h a| ≤ M) :
    |∑ a : α, (p a).toReal * h a| ≤ M := by
  classical
  calc
    |∑ a : α, (p a).toReal * h a| ≤
        ∑ a : α, |(p a).toReal * h a| :=
      finite_abs_sum_le_sum_abs Finset.univ
        (fun a : α => (p a).toReal * h a)
    _ = ∑ a : α, (p a).toReal * |h a| := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ a : α, (p a).toReal * M := by
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_left (hM a) ENNReal.toReal_nonneg
    _ = M := by
      rw [← Finset.sum_mul, finite_pmf_sum_toReal_eq_one]
      simp

/-- The difference of two finite PMF expectations of the same bounded test
function is controlled by the `L¹` distance between their real masses. -/
theorem finite_pmf_expectation_difference_abs_le_l1_mul_bound
    {α : Type*} [Fintype α]
    (p q : PMF α) (h : α → ℝ) (M : ℝ)
    (hM : ∀ a : α, |h a| ≤ M) :
    |(∑ a : α, (p a).toReal * h a) -
        ∑ a : α, (q a).toReal * h a| ≤
      (∑ a : α, |(p a).toReal - (q a).toReal|) * M := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a : α,
        ((p a).toReal * h a - (q a).toReal * h a)| =
      |∑ a : α,
        ((p a).toReal - (q a).toReal) * h a| := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ ≤ ∑ a : α,
        |((p a).toReal - (q a).toReal) * h a| :=
      finite_abs_sum_le_sum_abs Finset.univ
        (fun a : α => ((p a).toReal - (q a).toReal) * h a)
    _ = ∑ a : α,
        |(p a).toReal - (q a).toReal| * |h a| := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [abs_mul]
    _ ≤ ∑ a : α,
        |(p a).toReal - (q a).toReal| * M := by
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_left (hM a) (abs_nonneg _)
    _ = (∑ a : α, |(p a).toReal - (q a).toReal|) * M := by
      rw [Finset.sum_mul]

/-- Centering a finite PMF test function around any real number converts a
radius bound into the standard total-variation expectation bound. -/
theorem finite_pmf_expectation_difference_abs_le_two_mul_tv_mul_radius
    {α : Type*} [Fintype α]
    (p q : PMF α) (h : α → ℝ)
    (center radius : ℝ)
    (hRadius : ∀ a : α, |h a - center| ≤ radius) :
    |(∑ a : α, (p a).toReal * h a) -
        ∑ a : α, (q a).toReal * h a| ≤
      (∑ a : α, |(p a).toReal - (q a).toReal|) * radius := by
  classical
  have hShift (r : PMF α) :
      ∑ a : α, (r a).toReal * (h a - center) =
        (∑ a : α, (r a).toReal * h a) - center := by
    calc
      ∑ a : α, (r a).toReal * (h a - center) =
          ∑ a : α,
            ((r a).toReal * h a - (r a).toReal * center) := by
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = (∑ a : α, (r a).toReal * h a) -
          ∑ a : α, (r a).toReal * center := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ a : α, (r a).toReal * h a) - center := by
        rw [← Finset.sum_mul, finite_pmf_sum_toReal_eq_one]
        simp
  have hCenter :
      (∑ a : α, (p a).toReal * h a) -
          ∑ a : α, (q a).toReal * h a =
        ((∑ a : α, (p a).toReal * h a) - center) -
          ((∑ a : α, (q a).toReal * h a) - center) := by
    ring
  rw [hCenter, ← hShift p, ← hShift q]
  exact finite_pmf_expectation_difference_abs_le_l1_mul_bound
    p q (fun a => h a - center) radius hRadius

/-- For one Wilson conditional law, the common-test expectation difference is
controlled exactly by twice the conditional total variation times a fiber
radius. -/
theorem finite_lattice_singleLinkConditionalPMF_test_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (target : L.Edge)
    (h : L.Gauge → ℝ) (center radius : ℝ)
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
      unfold FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
      ring

/-- A Dobrushin matrix entry controls the common-test conditional expectation
change whenever the two environments differ only at the declared source link. -/
theorem finite_lattice_dobrushin_conditionalPMF_test_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source)
    (h : L.Gauge → ℝ) (center radius : ℝ)
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
      finite_lattice_singleLinkConditionalPMF_test_difference_abs_le
        L A B target h center radius hRadius
    _ ≤ 2 * D.influence target source * radius := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTV (by norm_num)) hRadiusNonneg

/-- Local Dobrushin propagation for Wilson conditional expectations.  The first
term measures the direct change of the observable when the source link is
changed; the second term measures the change of the target conditional law. -/
theorem finite_lattice_dobrushin_singleLinkConditionalExpectation_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
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
    exact finite_lattice_dobrushin_conditionalPMF_test_difference_abs_le
      L D target source A B hAgree hB center targetRadius
      hTargetRadiusNonneg (by
        intro g
        simpa [hB] using hTargetRadius g)
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
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
            ∑ g : L.Gauge, (pB g).toReal * hB g) := by
          ring
      _ = (∑ g : L.Gauge, (pA g).toReal * (hA g - hB g)) +
          ((∑ g : L.Gauge, (pA g).toReal * hB g) -
            ∑ g : L.Gauge, (pB g).toReal * hB g) := by
        rw [hFirst]
  rw [hSplit]
  exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

end

end MathlibAnalytic
end MGAP4D
