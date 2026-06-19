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

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

theorem action_comp_interpolate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (n : ℕ)
    (g : G.Symmetry) :
    G.action g ∘ E.interpolate n =
      E.interpolate n ∘
        (E.system n).base.gaugeTransform (G.latticeGauge n g) := by
  funext U
  exact (G.interpolate_equivariant n g U).symm

theorem embeddedMeasure_toMeasure_eq
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (n : ℕ) :
    (E.toLatticeEmbedding.embeddedMeasure n :
      Measure E.PhysicalConfiguration) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
  rfl

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D
