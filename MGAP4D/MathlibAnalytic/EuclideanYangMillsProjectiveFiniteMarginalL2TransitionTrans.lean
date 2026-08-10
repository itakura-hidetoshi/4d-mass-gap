import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderIsometricSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace EuclideanYangMillsProjectiveLimitMeasure

variable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Finite-marginal `L²` transition maps compose exactly along inclusions.

Rather than unfolding `Lp.compMeasurePreservingₗᵢ`, the proof uses the common
projective-limit `L²` carrier: both iterated and direct transitions have the
same continuum pullback, and the large-marginal pullback is injective. -/
theorem finiteMarginalL2Transition_trans
    {I J K : Finset EuclideanFourSpace}
    (hKJ : J ⊆ K)
    (hIK : K ⊆ I)
    (f : Lp ℝ 2 (F.finiteMarginal J)) :
    EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) hIK
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hKJ f) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) (hKJ.trans hIK) f := by
  apply L.finiteMarginalL2Pullback_injective I
  calc
    L.finiteMarginalL2Pullback I
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hIK
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hKJ f)) =
      L.finiteMarginalL2Pullback K
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hKJ f) :=
      (L.finiteMarginalL2Pullback_compatible hIK
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hKJ f)).symm
    _ = L.finiteMarginalL2Pullback J f :=
      (L.finiteMarginalL2Pullback_compatible hKJ f).symm
    _ = L.finiteMarginalL2Pullback I
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) (hKJ.trans hIK) f) :=
      L.finiteMarginalL2Pullback_compatible (hKJ.trans hIK) f

end EuclideanYangMillsProjectiveLimitMeasure

end

end MathlibAnalytic
end MGAP4D
