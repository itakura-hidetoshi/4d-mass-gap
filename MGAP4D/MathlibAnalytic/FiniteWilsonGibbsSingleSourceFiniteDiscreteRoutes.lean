import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveMarginals
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Every finite discrete Wilson field-value carrier is standard Borel. -/
theorem finite_wilson_single_source_fieldValue_standardBorel
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) := by
  letI : Countable (R.fieldValue x) := Fintype.toCountable _
  infer_instance

end

end MathlibAnalytic
end MGAP4D
