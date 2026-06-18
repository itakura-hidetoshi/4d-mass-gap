import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Analysis.SpecificLimits.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A finite extended-nonnegative constant divided by the canonical radii
`n + 1` tends to zero. -/
theorem ennreal_tendsto_const_div_natCast_add_one
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ≥0∞)) atTop (nhds 0) := by
  have hNN :
      Tendsto (fun n : ℕ => C.toNNReal / (n : ℝ≥0)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C.toNNReal
  have hShift :
      Tendsto (fun n : ℕ => C.toNNReal / ((n + 1 : ℕ) : ℝ≥0))
        atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hNN
  have hCoe :
      Tendsto
        (fun n : ℕ =>
          ((C.toNNReal / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞))
        atTop (nhds 0) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hShift
  simpa [← ENNReal.coe_toNNReal hC] using hCoe

end

end MathlibAnalytic
end MGAP4D
