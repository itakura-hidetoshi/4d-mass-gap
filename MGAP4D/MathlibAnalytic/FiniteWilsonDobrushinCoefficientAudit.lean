import MGAP4D.MathlibAnalytic.FiniteWilsonScaledHeatBathSweepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem exactGapValueReal_not_le_one_sub_nonnegative_coefficient
    {c : ℝ} (hc : 0 ≤ c) :
    ¬ exactGapValueReal ≤ 1 - c :=
  exactGapValueReal_not_le_one_sub_of_nonneg hc

end

end MathlibAnalytic
end MGAP4D
