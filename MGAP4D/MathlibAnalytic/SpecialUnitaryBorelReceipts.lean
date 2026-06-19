import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

@[reducible]
def specialUnitaryAmbientMatrixSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

@[reducible]
def specialUnitaryGroupSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    specialUnitaryAmbientMatrixSecondCountableTopology N
  exact TopologicalSpace.secondCountableTopology_induced
    (SpecialUnitaryMatrixGroup N)
    (Matrix (Fin N) (Fin N) ℂ)
    ((↑) : SpecialUnitaryMatrixGroup N → Matrix (Fin N) (Fin N) ℂ)

@[reducible]
def specialUnitaryGroupMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  borel (SpecialUnitaryMatrixGroup N)

@[reducible]
def specialUnitaryGroupBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) := by
  constructor
  rfl

end

end MathlibAnalytic
end MGAP4D
