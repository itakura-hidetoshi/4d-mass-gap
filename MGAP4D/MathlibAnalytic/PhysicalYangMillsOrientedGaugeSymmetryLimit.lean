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
    ProbabilityMeasure.toMeasure (E.toLatticeEmbedding.embeddedMeasure n) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
  rfl

theorem embeddedMeasure_toMeasure_map_eq_self
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (n : ℕ)
    (g : G.Symmetry) :
    Measure.map (G.action g)
        (ProbabilityMeasure.toMeasure
          (E.toLatticeEmbedding.embeddedMeasure n)) =
      ProbabilityMeasure.toMeasure
        (E.toLatticeEmbedding.embeddedMeasure n) := by
  have hGaugeMeasurable :
      Measurable
        ((E.system n).base.gaugeTransform (G.latticeGauge n g)) :=
    (continuous_compact_oriented_gibbs_measurePreserving
      (E.system n) (G.latticeGauge n g)).measurable
  change
    Measure.map (G.action g)
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure
  calc
    Measure.map (G.action g)
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
        Measure.map (G.action g ∘ E.interpolate n)
          (E.system n).gibbsMeasure :=
      Measure.map_map (G.action_continuous g).measurable
        (E.interpolate_measurable n)
    _ = Measure.map
          (E.interpolate n ∘
            (E.system n).base.gaugeTransform (G.latticeGauge n g))
          (E.system n).gibbsMeasure := by
      rw [G.action_comp_interpolate n g]
    _ = Measure.map (E.interpolate n)
          (Measure.map
            ((E.system n).base.gaugeTransform (G.latticeGauge n g))
            (E.system n).gibbsMeasure) :=
      (Measure.map_map (E.interpolate_measurable n) hGaugeMeasurable).symm
    _ = Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
      rw [continuous_compact_oriented_gibbs_map_eq_self]

theorem embeddedMeasure_map_eq_self
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (n : ℕ)
    (g : G.Symmetry) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (G.action_continuous g).measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  exact G.embeddedMeasure_toMeasure_map_eq_self n g

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D
