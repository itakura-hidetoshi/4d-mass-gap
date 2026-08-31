import MGAP4D.MathlibAnalytic.DenseLinearIsometryClosedSubspaceCorestriction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    {C E : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization S) :
    DenseRange R.corestrict :=
  R.corestrict_denseRange

end

end MathlibAnalytic
end MGAP4D
