import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactEnergyMaximum
import Mathlib.Data.ENNReal.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory Set

noncomputable section

/-- The finite sum of one compactness-generated plaquette maximum is exactly
its plaquette-cardinality multiple. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.compactPlaquetteMaximum_sum_eq_card_mul
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ) :
    (∑ _p : (E.system n).base.Plaquette,
        E.compactPlaquetteEnergyMaximum n) =
      ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) *
        E.compactPlaquetteEnergyMaximum n := by
  simp

end

end MathlibAnalytic
end MGAP4D
