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

end

end MathlibAnalytic
end MGAP4D
