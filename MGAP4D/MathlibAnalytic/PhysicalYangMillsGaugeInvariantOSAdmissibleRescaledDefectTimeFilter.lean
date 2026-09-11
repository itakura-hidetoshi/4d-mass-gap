import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullGraphSumNormApproximation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The admissible small-positive-time filter is nontrivial.  Its subtype
projection has eventually full range because the linear defect lower bound
holds at every sufficiently small positive time. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTimeFilter_neBot
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) :
    G.admissibleRescaledDefectTimeFilter.NeBot := by
  let projection : G.AdmissibleRescaledDefectTime → NNReal := fun tau => tau.1
  have hRange :
      Set.range projection ∈ nhdsWithin (0 : NNReal) (Ioi 0) := by
    filter_upwards
      [G.eventually_linear_defect_lower_bound T, self_mem_nhdsWithin]
        with t hLinear htPos
    exact ⟨⟨t, htPos, hLinear⟩, rfl⟩
  rw [Filter.neBot_iff]
  intro hBot
  have hMapped := congrArg (Filter.map projection) hBot
  rw [VacuumSemigroupGapSlope.admissibleRescaledDefectTimeFilter,
    Filter.map_bot, Filter.map_comap_of_mem hRange] at hMapped
  exact (show (nhdsWithin (0 : NNReal) (Ioi 0)).NeBot from inferInstance).ne hMapped

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
