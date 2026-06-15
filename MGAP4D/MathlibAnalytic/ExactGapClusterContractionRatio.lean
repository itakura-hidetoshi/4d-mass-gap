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
  have hneg : -exactGapValueReal < 0 := neg_neg_of_pos exactGapValueReal_pos
  have hexp : Real.exp (-exactGapValueReal) < Real.exp 0 :=
    Real.exp_lt_exp.mpr hneg
  simpa using hexp

end

end MathlibAnalytic
end MGAP4D
