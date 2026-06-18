import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Analysis.SpecificLimits.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The nonnegative-real canonical reciprocal tail. -/
theorem nnreal_tendsto_const_div_nat
    (C : ℝ≥0) :
    Tendsto (fun n : ℕ => C / (n : ℝ≥0)) atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat C

end

end MathlibAnalytic
end MGAP4D
