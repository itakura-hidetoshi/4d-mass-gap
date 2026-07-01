import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Every finite oriented Wilson Gibbs atom has strictly positive real mass. -/
theorem finite_oriented_gibbsProbabilityReal_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 < L.gibbsProbabilityReal A := by
  unfold FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  rw [ENNReal.toReal_pos]
  constructor
  · rw [finite_oriented_gibbsPMF_apply]
    exact mul_ne_zero
      (finite_oriented_boltzmannWeight_ne_zero L A)
      (inv_ne_zero (finite_oriented_partitionFunction_ne_top L))
  · exact (L.gibbsPMF).apply_ne_top A

/-- Full support makes finite Gibbs variance definite: two configurations with
unequal observable values force strictly positive variance. -/
theorem finite_oriented_gibbsVarianceReal_pos_of_exists_ne
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (hNe : f A ≠ f B) :
    0 < L.gibbsVarianceReal f := by
  classical
  let m : ℝ := L.gibbsExpectationReal f
  have hAorB : f A ≠ m ∨ f B ≠ m := by
    by_contra h
    push_neg at h
    exact hNe (h.1.trans h.2.symm)
  unfold FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
  rcases hAorB with hA | hB
  · have hTermPos :
        0 < L.gibbsProbabilityReal A * (f A - m) ^ 2 := by
      exact mul_pos
        (finite_oriented_gibbsProbabilityReal_pos L A)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hA))
    have hTermLe :
        L.gibbsProbabilityReal A * (f A - m) ^ 2 ≤
          ∑ C : L.Configuration,
            L.gibbsProbabilityReal C * (f C - m) ^ 2 := by
      exact Finset.single_le_sum
        (fun C _ => mul_nonneg
          (finite_oriented_gibbsProbabilityReal_nonneg L C)
          (sq_nonneg _))
        (Finset.mem_univ A)
    exact lt_of_lt_of_le hTermPos hTermLe
  · have hTermPos :
        0 < L.gibbsProbabilityReal B * (f B - m) ^ 2 := by
      exact mul_pos
        (finite_oriented_gibbsProbabilityReal_pos L B)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hB))
    have hTermLe :
        L.gibbsProbabilityReal B * (f B - m) ^ 2 ≤
          ∑ C : L.Configuration,
            L.gibbsProbabilityReal C * (f C - m) ^ 2 := by
      exact Finset.single_le_sum
        (fun C _ => mul_nonneg
          (finite_oriented_gibbsProbabilityReal_nonneg L C)
          (sq_nonneg _))
        (Finset.mem_univ B)
    exact lt_of_lt_of_le hTermPos hTermLe

/-- For a full-support finite oriented Wilson law, zero variance is equivalent
to pointwise constancy of the observable. -/
theorem finite_oriented_gibbsVarianceReal_eq_zero_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsVarianceReal f = 0 ↔ ∀ A B, f A = f B := by
  constructor
  · intro hZero A B
    by_contra hNe
    have hPos := finite_oriented_gibbsVarianceReal_pos_of_exists_ne L f A B hNe
    linarith
  · intro hConst
    have hPoint : ∀ A, f A = L.gibbsExpectationReal f := by
      intro A
      unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
      calc
        f A = ∑ B : L.Configuration,
            L.gibbsProbabilityReal B * f A := by
          rw [← Finset.sum_mul]
          have hMass :
              ∑ B : L.Configuration, L.gibbsProbabilityReal B = 1 := by
            simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
              finite_oriented_pmf_sum_toReal_eq_one L.gibbsPMF
          rw [hMass, one_mul]
        _ = ∑ B : L.Configuration,
            L.gibbsProbabilityReal B * f B := by
          apply Finset.sum_congr rfl
          intro B _
          rw [hConst A B]
    unfold FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
    apply Finset.sum_eq_zero
    intro A _
    rw [hPoint A, sub_self, zero_pow]
    simp

end

end MathlibAnalytic
end MGAP4D
