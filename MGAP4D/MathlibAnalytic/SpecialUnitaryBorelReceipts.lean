import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Second countability inherited from the finite-dimensional matrix space. -/
def specialUnitaryGroupSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) := by
  infer_instance

/-- The measurable structure inherited from the ambient matrix space. -/
def specialUnitaryGroupMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) := by
  infer_instance

/-- The inherited measurable structure is the Borel structure. -/
def specialUnitaryGroupBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) := by
  infer_instance

end

end MathlibAnalytic
end MGAP4D
