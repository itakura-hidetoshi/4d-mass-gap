import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonActionPointwiseBound

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) where
  Symmetry : Type
  action : Symmetry → E.PhysicalConfiguration → E.PhysicalConfiguration
  action_continuous : ∀ g, Continuous (action g)
  latticeGauge : ∀ n, Symmetry → (E.system n).base.GaugeTransformation
  interpolate_equivariant : ∀ n g U,
    E.interpolate n ((E.system n).base.gaugeTransform (latticeGauge n g) U) =
      action g (E.interpolate n U)

end

end MathlibAnalytic
end MGAP4D
