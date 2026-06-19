import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonGaugeInvariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The automatically normalized finite-volume compact oriented Wilson Gibbs
law bundled as a Mathlib probability measure. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ProbabilityMeasure C.base.Configuration :=
  ⟨C.gibbsMeasure,
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C⟩

@[simp]
theorem continuous_compact_oriented_gibbsProbabilityMeasure_toMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    (C.gibbsProbabilityMeasure : Measure C.base.Configuration) =
      C.gibbsMeasure :=
  rfl

/-- A sequence of signed-boundary compact-gauge Wilson systems, each defined on
physical positive links, together with interpolation into one fixed physical
Polish carrier. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding where
  PhysicalConfiguration : Type
  [physicalTopologicalSpace : TopologicalSpace PhysicalConfiguration]
  [physicalMeasurableSpace : MeasurableSpace PhysicalConfiguration]
  [physicalBorelSpace : BorelSpace PhysicalConfiguration]
  [physicalPolishSpace : PolishSpace PhysicalConfiguration]
  system : ℕ → ContinuousCompactOrientedGaugeWilsonSystem
  interpolate :
    ∀ n, (system n).base.Configuration → PhysicalConfiguration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop :
    Tendsto physicalVolume atTop atTop

attribute [instance]
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.physicalTopologicalSpace
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.physicalMeasurableSpace
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.physicalBorelSpace
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.physicalPolishSpace

/-- Forget the oriented Wilson origin while retaining the actual finite-volume
probability laws, interpolation maps, and physical scaling data. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.toLatticeEmbedding
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) :
    PhysicalFourDimensionalYangMillsLatticeEmbedding :=
  { PhysicalConfiguration := E.PhysicalConfiguration
    LatticeConfiguration := fun n => (E.system n).base.Configuration
    latticeMeasure := fun n => (E.system n).gibbsProbabilityMeasure
    interpolate := E.interpolate
    interpolate_measurable := E.interpolate_measurable
    latticeSpacing := E.latticeSpacing
    latticeSpacing_pos := E.latticeSpacing_pos
    latticeSpacing_tendsto_zero := E.latticeSpacing_tendsto_zero
    physicalVolume := E.physicalVolume
    physicalVolume_tendsto_atTop := E.physicalVolume_tendsto_atTop }

/-- The embedded law at scale `n` is exactly the pushforward of the
orientation-correct finite-volume Gibbs probability measure. -/
theorem continuous_compact_oriented_gauge_wilson_embeddedMeasure_eq
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (n : ℕ) :
    E.toLatticeEmbedding.embeddedMeasure n =
      (E.system n).gibbsProbabilityMeasure.map
        (E.interpolate_measurable n).aemeasurable :=
  rfl

/-- A weakly convergent sequence of interpolated oriented Wilson laws produces
an actual physical four-dimensional Yang--Mills weak-limit carrier. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.toWeakLimit
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.toLatticeEmbedding.embeddedMeasure atTop
        (nhds continuumMeasure)) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  E.toLatticeEmbedding.toWeakLimit continuumMeasure hWeak

end

end MathlibAnalytic
end MGAP4D
