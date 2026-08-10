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
  apply (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback
    L I).injective
  calc
    EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback L I
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hIK
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hKJ f)) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback L K
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hKJ f) :=
      (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback_compatible
        L hIK
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hKJ f)).symm
    _ = EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback L J f :=
      (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback_compatible
        L hKJ f).symm
    _ = EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback L I
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) (hKJ.trans hIK) f) :=
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback_compatible
        L (hKJ.trans hIK) f

end EuclideanYangMillsProjectiveLimitMeasure

end

end MathlibAnalytic
end MGAP4D
