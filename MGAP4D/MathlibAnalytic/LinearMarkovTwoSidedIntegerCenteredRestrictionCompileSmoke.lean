import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerCenteredRestriction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

example {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerCenteredPathRestriction n) =
      (linearMarkovIntegerCenteredFinitePathPMF initial transition n).toMeasure :=
  linearMarkovTwoSidedIntegerPathMeasure_map_centeredRestriction
    initial transition hdb n

end

end MathlibAnalytic
end MGAP4D
