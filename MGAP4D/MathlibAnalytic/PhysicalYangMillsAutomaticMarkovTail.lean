import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Compile gate for Mathlib's canonical ENNReal inverse sequence limit. -/
theorem ennreal_tendsto_inv_nat_compile_smoke :
    Tendsto (fun n : ℕ => ((n : ℝ≥0∞))⁻¹) atTop (nhds 0) :=
  ENNReal.tendsto_inv_nat_nhds_zero

end

end MathlibAnalytic
end MGAP4D
