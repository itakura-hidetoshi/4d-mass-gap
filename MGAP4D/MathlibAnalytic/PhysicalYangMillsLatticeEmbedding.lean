import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- A sequence of lattice probability spaces embedded into one fixed physical
Polish configuration space.

This is the missing typed bridge between finite lattice Wilson measures, whose
configuration types vary with the lattice, and a genuine continuum weak limit
on one common distributional carrier. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding where
  PhysicalConfiguration : Type
  [physicalTopologicalSpace : TopologicalSpace PhysicalConfiguration]
  [physicalMeasurableSpace : MeasurableSpace PhysicalConfiguration]
  [physicalBorelSpace : BorelSpace PhysicalConfiguration]
  [physicalPolishSpace : PolishSpace PhysicalConfiguration]
  LatticeConfiguration : ℕ → Type
  [latticeMeasurableSpace : ∀ n, MeasurableSpace (LatticeConfiguration n)]
  latticeMeasure : ∀ n, ProbabilityMeasure (LatticeConfiguration n)
  interpolate : ∀ n, LatticeConfiguration n → PhysicalConfiguration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop :
    Tendsto physicalVolume atTop atTop

attribute [instance]
  PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalTopologicalSpace
  PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalMeasurableSpace
  PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalBorelSpace
  PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalPolishSpace
  PhysicalFourDimensionalYangMillsLatticeEmbedding.latticeMeasurableSpace

/-- Push one lattice law through its interpolation map into the fixed physical
configuration space. -/
noncomputable def
    PhysicalFourDimensionalYangMillsLatticeEmbedding.embeddedMeasure
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (n : ℕ) : ProbabilityMeasure E.PhysicalConfiguration :=
  (E.latticeMeasure n).map (E.interpolate_measurable n).aemeasurable

/-- Once the pushed-forward lattice laws converge weakly, the generic lattice
embedding produces the physical four-dimensional Yang--Mills weak-limit
carrier. -/
noncomputable def
    PhysicalFourDimensionalYangMillsLatticeEmbedding.toWeakLimit
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak : Tendsto E.embeddedMeasure atTop (nhds continuumMeasure)) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  { Configuration := E.PhysicalConfiguration
    approximatingMeasure := E.embeddedMeasure
    continuumMeasure := continuumMeasure
    weakConvergence := hWeak
    latticeSpacing := E.latticeSpacing
    latticeSpacing_pos := E.latticeSpacing_pos
    latticeSpacing_tendsto_zero := E.latticeSpacing_tendsto_zero
    physicalVolume := E.physicalVolume
    physicalVolume_tendsto_atTop := E.physicalVolume_tendsto_atTop }

/-- A concrete sequence of automatically normalized continuous compact-gauge
Wilson Gibbs systems together with interpolation maps into a fixed physical
Polish carrier. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding where
  PhysicalConfiguration : Type
  [physicalTopologicalSpace : TopologicalSpace PhysicalConfiguration]
  [physicalMeasurableSpace : MeasurableSpace PhysicalConfiguration]
  [physicalBorelSpace : BorelSpace PhysicalConfiguration]
  [physicalPolishSpace : PolishSpace PhysicalConfiguration]
  system : ℕ → ContinuousCompactGaugeWilsonSystem
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
  ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalTopologicalSpace
  ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalMeasurableSpace
  ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalBorelSpace
  ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalPolishSpace

/-- Forget the concrete Wilson origin while retaining the actual Gibbs laws and
all interpolation/scaling data. -/
noncomputable def
    ContinuousCompactGaugeWilsonPhysicalEmbedding.toLatticeEmbedding
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) :
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

/-- The embedded approximation at scale `n` is exactly the pushforward of the
finite-volume Wilson Gibbs probability law. -/
theorem continuous_compact_gauge_wilson_embeddedMeasure_eq
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ) :
    E.toLatticeEmbedding.embeddedMeasure n =
      (E.system n).gibbsProbabilityMeasure.map
        (E.interpolate_measurable n).aemeasurable :=
  rfl

/-- A weakly convergent sequence of interpolated Wilson Gibbs laws produces an
actual continuum probability measure with `a_n → 0` and physical volume tending
to infinity. -/
noncomputable def
    ContinuousCompactGaugeWilsonPhysicalEmbedding.toWeakLimit
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.toLatticeEmbedding.embeddedMeasure atTop
        (nhds continuumMeasure)) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  E.toLatticeEmbedding.toWeakLimit continuumMeasure hWeak

end

end MathlibAnalytic
end MGAP4D
