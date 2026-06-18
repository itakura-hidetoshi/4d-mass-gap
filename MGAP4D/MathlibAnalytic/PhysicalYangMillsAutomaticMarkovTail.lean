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
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)) atTop (nhds ∞) := by
    apply ENNReal.tendsto_nhds_top
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    exact_mod_cast Nat.lt_succ_of_le hn
  have hTail := ENNReal.Tendsto.const_div hRadius (Or.inr hC)
  simpa using hTail

end

end MathlibAnalytic
end MGAP4D
