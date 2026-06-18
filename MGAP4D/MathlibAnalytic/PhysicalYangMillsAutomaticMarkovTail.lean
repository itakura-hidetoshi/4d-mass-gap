import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A finite extended-nonnegative constant divided by the canonical radii
`n + 1` tends to zero. -/
theorem ennreal_tendsto_const_div_natCast_add_one
    (C : ENNReal) (hC : C ≠ ⊤) :
    Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ENNReal)) atTop (nhds 0) := by
  have hInv :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ENNReal))⁻¹) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  have hMul :
      Tendsto
        (fun n : ℕ => C * (((n + 1 : ℕ) : ENNReal))⁻¹)
        atTop (nhds (C * 0)) :=
    ENNReal.Tendsto.const_mul hInv (Or.inr hC)
  simpa [div_eq_mul_inv] using hMul

end

end MathlibAnalytic
end MGAP4D
