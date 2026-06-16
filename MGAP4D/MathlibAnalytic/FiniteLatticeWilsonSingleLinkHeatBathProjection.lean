import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite probability mass function has total real mass one. -/
theorem finite_pmf_sum_toReal_eq_one
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  classical
  have hToReal :
      (∑ a : α, (p a).toReal) =
        (ENNReal.toReal (∑ a : α, p a)) := by
    symm
    simpa using
      (ENNReal.toReal_sum
        (s := Finset.univ)
        (f := fun a : α => p a)
        (fun a _ha => p.apply_ne_top a))
  rw [hToReal]
  have hMass : (∑ a : α, p a) = (1 : ℝ≥0∞) := by
    rw [← tsum_fintype]
    exact p.tsum_coe
  rw [hMass]
  simp

end

end MathlibAnalytic
end MGAP4D
