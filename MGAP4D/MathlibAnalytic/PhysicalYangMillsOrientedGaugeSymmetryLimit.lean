import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonActionPointwiseBound

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- A continuous symmetry action on the common physical carrier, realized at
every lattice scale by a vertex gauge transformation and intertwined by the
interpolation map. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) where
  Symmetry : Type
  action : Symmetry → E.PhysicalConfiguration → E.PhysicalConfiguration
  action_continuous : ∀ g, Continuous (action g)
  latticeGauge :
    ∀ n, Symmetry → (E.system n).base.GaugeTransformation
  interpolate_equivariant :
    ∀ n g U,
      E.interpolate n
          ((E.system n).base.gaugeTransform (latticeGauge n g) U) =
        action g (E.interpolate n U)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

/-- Interpolation equivariance and finite-volume gauge invariance imply that
every embedded physical lattice law is invariant under the continuous physical
action. -/
theorem embeddedMeasure_map_eq_self
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (n : ℕ)
    (g : G.Symmetry) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (G.action_continuous g).measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (G.action g)
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure
  have hGaugeMeas :
      Measurable
        ((E.system n).base.gaugeTransform (G.latticeGauge n g)) :=
    (continuous_compact_oriented_gibbs_measurePreserving
      (E.system n) (G.latticeGauge n g)).measurable
  have hIntertwine :
      G.action g ∘ E.interpolate n =
        E.interpolate n ∘
          (E.system n).base.gaugeTransform (G.latticeGauge n g) := by
    funext U
    exact (G.interpolate_equivariant n g U).symm
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
      rw [hIntertwine]
    _ = Measure.map (E.interpolate n)
          (Measure.map
            ((E.system n).base.gaugeTransform (G.latticeGauge n g))
            (E.system n).gibbsMeasure) :=
      (Measure.map_map (E.interpolate_measurable n) hGaugeMeas).symm
    _ = Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
      rw [continuous_compact_oriented_gibbs_map_eq_self]

/-- Tightness plus scale-wise interpolation-equivariant gauge invariance produces
a symmetry-enhanced Prokhorov weak limit. -/
noncomputable def toSymmetryLimit
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsSymmetryLimit := by
  let L :=
    (physical_yang_mills_prokhorov_subsequence_exists
      E.toLatticeEmbedding hTight).some
  exact
    { Configuration := E.PhysicalConfiguration
      approximatingMeasure := fun n =>
        E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)
      continuumMeasure := L.continuumMeasure
      weakConvergence := L.weakConvergence
      latticeSpacing := fun n =>
        E.latticeSpacing (L.subsequence n)
      latticeSpacing_pos := fun n =>
        E.latticeSpacing_pos (L.subsequence n)
      latticeSpacing_tendsto_zero :=
        E.latticeSpacing_tendsto_zero.comp
          L.subsequence_strictMono.tendsto_atTop
      physicalVolume := fun n =>
        E.physicalVolume (L.subsequence n)
      physicalVolume_tendsto_atTop :=
        E.physicalVolume_tendsto_atTop.comp
          L.subsequence_strictMono.tendsto_atTop
      Symmetry := G.Symmetry
      action := G.action
      action_continuous := G.action_continuous
      approximatingInvariant := fun n g =>
        G.embeddedMeasure_map_eq_self (L.subsequence n) g }

/-- The continuum probability measure selected by Prokhorov is automatically
invariant under every physical gauge symmetry represented equivariantly at all
lattice scales. -/
theorem continuumMeasure_map_eq_self
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (hTight : E.toLatticeEmbedding.IsTight)
    (g : G.Symmetry) :
    (G.toSymmetryLimit hTight).continuumMeasure.map
        (G.action_continuous g).measurable.aemeasurable =
      (G.toSymmetryLimit hTight).continuumMeasure :=
  physical_yang_mills_symmetry_passes_to_weak_limit
    (G.toSymmetryLimit hTight) g

/-- A deterministic signed-action bound and physical coercivity now produce a
physical weak limit whose continuum law retains the represented gauge
symmetries. -/
noncomputable def toSymmetryLimit_of_actionPointwiseBound
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (G : E.PhysicalGaugeAction)
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsSymmetryLimit :=
  G.toSymmetryLimit (B.isTight D)

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D
