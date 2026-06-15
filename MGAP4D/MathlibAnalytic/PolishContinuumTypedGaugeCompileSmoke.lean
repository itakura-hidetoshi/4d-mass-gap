import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishProjectiveContinuumConstructionFixed

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {F : EuclideanYangMillsProjectiveCylinderFamily}
  [∀ x, TopologicalSpace (F.fieldValue x)]
  [∀ x, BorelSpace (F.fieldValue x)]
  [∀ x, PolishSpace (F.fieldValue x)]

theorem polish_continuum_typed_gauge_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticDataFixed F) :
    IsProjectiveLimit
      D.toContinuumConstruction.limit.continuumMeasure
      F.finiteMarginal :=
  D.projectiveLimit

end

end MathlibAnalytic
end MGAP4D
