import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {α : Type*} [Fintype α]

example (p : PMF α) :
    ∑ a : α, p a = 1 :=
  finite_pmf_sum_eq_one p

example (p : PMF α) :
    ∑ a : α, (p a).toReal =
      ENNReal.toReal (∑ a : α, p a) :=
  finite_pmf_sum_toReal_eq_toReal_sum p

example (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 :=
  finite_pmf_sum_toReal_eq_one p

end

end MathlibAnalytic
end MGAP4D
