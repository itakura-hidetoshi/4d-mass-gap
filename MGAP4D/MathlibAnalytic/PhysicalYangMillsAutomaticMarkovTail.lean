import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A finite extended-nonnegative constant divided by the canonical radii
`n + 1` tends to zero. -/
theorem ennreal_tendsto_const_div_natCast_add_one
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ≥0∞)) atTop (nhds 0) := by
  have hRadius :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)) atTop (nhds ∞) :=
    (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_nat_nhds_top
  simpa using ENNReal.Tendsto.const_div hRadius (Or.inr hC)

end

end MathlibAnalytic
end MGAP4D
