import MGAP4D.MathlibAnalytic.DenseLinearIsometryClosedSubspaceCorestriction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    {C E : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S) :
    DenseRange
      (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
        (C := C) (E := E) (S := S) R) :=
  RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange
    (C := C) (E := E) (S := S) R

end

end MathlibAnalytic
end MGAP4D
