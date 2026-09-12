import MGAP4D.MathlibAnalytic.FinitePMFRealExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The real point masses of a finite PMF sum to one. -/
theorem finitePMFRealWeight_sum_one
    {α : Type*} [Fintype α]
    (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  classical
  have hsum : ∑ a : α, p a = 1 := by
    simpa [tsum_fintype] using PMF.tsum_coe p
  calc
    ∑ a : α, (p a).toReal = (∑ a : α, p a).toReal := by
      symm
      rw [ENNReal.toReal_sum]
      intro a _ha
      exact p.apply_ne_top a
    _ = 1 := by rw [hsum]; simp

/-- Finite-PMF real expectation is monotone. -/
theorem finitePMFExpectationReal_mono
    {α : Type*} [Fintype α]
    (p : PMF α)
    {f g : α → ℝ}
    (hfg : ∀ a, f a ≤ g a) :
    finitePMFExpectationReal p f ≤ finitePMFExpectationReal p g := by
  classical
  unfold finitePMFExpectationReal
  apply Finset.sum_le_sum
  intro a _ha
  exact mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg

/-- Square Jensen inequality for real expectation under a finite PMF. -/
theorem finitePMFExpectationReal_sq_le_expectation_sq
    {α : Type*} [Fintype α]
    (p : PMF α)
    (f : α → ℝ) :
    (finitePMFExpectationReal p f) ^ 2 ≤
      finitePMFExpectationReal p (fun a => (f a) ^ 2) := by
  classical
  let m := finitePMFExpectationReal p f
  have hvar :
      0 ≤ ∑ a : α, (p a).toReal * (f a - m) ^ 2 :=
    Finset.sum_nonneg fun a _ha =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hsum : ∑ a : α, (p a).toReal = 1 :=
    finitePMFRealWeight_sum_one p
  have hm : ∑ a : α, (p a).toReal * f a = m := rfl
  have hsquare :
      ∑ a : α, (p a).toReal * (f a) ^ 2 =
        finitePMFExpectationReal p (fun a => (f a) ^ 2) := rfl
  have hexpand :
      (∑ a : α, (p a).toReal * (f a - m) ^ 2) =
        finitePMFExpectationReal p (fun a => (f a) ^ 2) - m ^ 2 := by
    calc
      (∑ a : α, (p a).toReal * (f a - m) ^ 2) =
          ∑ a : α,
            ((p a).toReal * (f a) ^ 2 +
              (-2 * m) * ((p a).toReal * f a) +
              m ^ 2 * (p a).toReal) := by
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = (∑ a : α, (p a).toReal * (f a) ^ 2) +
          (-2 * m) * (∑ a : α, (p a).toReal * f a) +
          m ^ 2 * (∑ a : α, (p a).toReal) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = finitePMFExpectationReal p (fun a => (f a) ^ 2) - m ^ 2 := by
        rw [hsquare, hm, hsum]
        ring
  rw [hexpand] at hvar
  simpa [m] using (sub_nonneg.mp hvar)

end

end MathlibAnalytic
end MGAP4D
