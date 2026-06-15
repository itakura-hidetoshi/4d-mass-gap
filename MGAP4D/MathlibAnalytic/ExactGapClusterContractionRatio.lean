import MGAP4D.MathlibAnalytic.ExactGapReal
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The one-step contraction ratio associated with the public positive exact-gap carrier. -/
def exactGapClusterContractionRatio : ℝ :=
  Real.exp (-exactGapValueReal)

/-- The exact-gap contraction ratio is strictly positive. -/
theorem exact_gap_cluster_contraction_ratio_pos :
    0 < exactGapClusterContractionRatio := by
  exact Real.exp_pos _

/-- The exact-gap contraction ratio is nonnegative. -/
theorem exact_gap_cluster_contraction_ratio_nonneg :
    0 ≤ exactGapClusterContractionRatio :=
  exact_gap_cluster_contraction_ratio_pos.le

/-- Positivity of the exact gap makes its exponential one-step ratio less than one. -/
theorem exact_gap_cluster_contraction_ratio_lt_one :
    exactGapClusterContractionRatio < 1 := by
  unfold exactGapClusterContractionRatio
  simpa only [Real.exp_zero] using
    Real.exp_strictMono (neg_lt_zero.mpr exactGapValueReal_pos)

end

end MathlibAnalytic
end MGAP4D
