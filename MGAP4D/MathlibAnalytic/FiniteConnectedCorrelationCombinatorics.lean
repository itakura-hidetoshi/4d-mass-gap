import MGAP4D.MathlibAnalytic.FiniteCumulantCombinatorics
import MGAP4D.MathlibAnalytic.TwoPointConnectedCorrelationAlgebra

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Connected finite correlation associated with a family of block moments.

For arbitrary finite order this is, by definition, the finite cumulant.  The
separate name records the Euclidean connected-correlation interpretation while
keeping higher cumulants distinct from centered products. -/
def finiteConnectedCorrelation
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) (moment : Finset α → R) : R :=
  finiteCumulant J moment

@[simp]
theorem finiteConnectedCorrelation_eq_finiteCumulant
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) (moment : Finset α → R) :
    finiteConnectedCorrelation J moment = finiteCumulant J moment := by
  rfl

/-- Pointwise equality of all block moments preserves the connected finite
correlation. -/
theorem finiteConnectedCorrelation_congr
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) {moment moment' : Finset α → R}
    (h : ∀ B, moment' B = moment B) :
    finiteConnectedCorrelation J moment' = finiteConnectedCorrelation J moment := by
  exact finiteCumulant_congr J h

end

end MathlibAnalytic
end MGAP4D
