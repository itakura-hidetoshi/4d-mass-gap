import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite probability mass function has total extended-nonnegative mass one. -/
theorem finite_pmf_sum_eq_one
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, p a = 1 := by
  classical
  simpa only [tsum_fintype] using p.tsum_coe

/-- Passing a finite probability mass function to real masses commutes with the
finite total sum. -/
theorem finite_pmf_sum_toReal_eq_toReal_sum
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal =
      ENNReal.toReal (∑ a : α, p a) := by
  classical
  exact
    (ENNReal.toReal_sum
      (s := Finset.univ)
      (f := fun a : α => p a)
      (fun a _ha => p.apply_ne_top a)).symm

/-- A finite probability mass function has total real mass one. -/
theorem finite_pmf_sum_toReal_eq_one
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  rw [finite_pmf_sum_toReal_eq_toReal_sum p,
    finite_pmf_sum_eq_one p]
  simp

end

end MathlibAnalytic
end MGAP4D
