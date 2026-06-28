import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- A physical continuum-limit carrier for four-dimensional Yang--Mills
probability measures.

All lattice measures have already been embedded into one fixed Polish
configuration space.  Thus `weakConvergence` is genuine convergence in law of
Mathlib `ProbabilityMeasure`s, rather than an abstract proposition or an
identification of one fixed finite system with a continuum label. -/
structure PhysicalFourDimensionalYangMillsWeakLimit where
  Configuration : Type
  [configurationTopologicalSpace : TopologicalSpace Configuration]
  [configurationMeasurableSpace : MeasurableSpace Configuration]
  [configurationBorelSpace : BorelSpace Configuration]
  [configurationPolishSpace : PolishSpace Configuration]
  approximatingMeasure : ℕ → ProbabilityMeasure Configuration
  continuumMeasure : ProbabilityMeasure Configuration
  weakConvergence :
    Tendsto approximatingMeasure atTop (nhds continuumMeasure)
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop :
    Tendsto physicalVolume atTop atTop

attribute [instance]
  PhysicalFourDimensionalYangMillsWeakLimit.configurationTopologicalSpace
  PhysicalFourDimensionalYangMillsWeakLimit.configurationMeasurableSpace
  PhysicalFourDimensionalYangMillsWeakLimit.configurationBorelSpace
  PhysicalFourDimensionalYangMillsWeakLimit.configurationPolishSpace

/-- The actual continuum Yang--Mills measure carried by a physical weak limit. -/
def PhysicalFourDimensionalYangMillsWeakLimit.measure
    (S : PhysicalFourDimensionalYangMillsWeakLimit) :
    Measure S.Configuration :=
  S.continuumMeasure

/-- The weak-limit carrier is automatically a probability measure. -/
theorem physical_yang_mills_weak_limit_isProbabilityMeasure
    (S : PhysicalFourDimensionalYangMillsWeakLimit) :
    IsProbabilityMeasure S.measure := by
  unfold PhysicalFourDimensionalYangMillsWeakLimit.measure
  infer_instance

/-- Weak convergence is exactly convergence of expectations of every bounded
continuous physical observable. -/
theorem physical_yang_mills_bounded_observable_expectation_converges
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O A ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, O A ∂(S.continuumMeasure : Measure S.Configuration))) := by
  exact
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      S.weakConvergence) O

/-- A symmetry acting continuously on the fixed physical configuration space,
with every embedded lattice law invariant under that action. -/
structure PhysicalFourDimensionalYangMillsSymmetryLimit
    extends PhysicalFourDimensionalYangMillsWeakLimit where
  Symmetry : Type
  action : Symmetry → Configuration → Configuration
  action_continuous : ∀ g, Continuous (action g)
  approximatingInvariant :
    ∀ (n : ℕ) (g : Symmetry),
      (approximatingMeasure n).map
          (action_continuous g).measurable.aemeasurable =
        approximatingMeasure n

/-- A continuous symmetry of every lattice approximation preserves the actual
weak-limit probability measure.  No independent continuum invariance receipt is
required. -/
theorem physical_yang_mills_symmetry_passes_to_weak_limit
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry) :
    S.continuumMeasure.map
        (S.action_continuous g).measurable.aemeasurable =
      S.continuumMeasure := by
  have hMapped :
      Tendsto
        (fun n : ℕ =>
          (S.approximatingMeasure n).map
            (S.action_continuous g).measurable.aemeasurable)
        atTop
        (nhds
          (S.continuumMeasure.map
            (S.action_continuous g).measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      S.approximatingMeasure S.continuumMeasure
      S.weakConvergence (S.action_continuous g)
  have hOriginal :
      Tendsto
        (fun n : ℕ =>
          (S.approximatingMeasure n).map
            (S.action_continuous g).measurable.aemeasurable)
        atTop
        (nhds S.continuumMeasure) := by
    simpa only [S.approximatingInvariant] using S.weakConvergence
  exact tendsto_nhds_unique hMapped hOriginal

/-- The automatically constructed finite-volume compact-gauge Wilson Gibbs
measure bundled as a Mathlib probability measure. -/
noncomputable def
    ContinuousCompactGaugeWilsonSystem.gibbsProbabilityMeasure
    (C : ContinuousCompactGaugeWilsonSystem) :
    ProbabilityMeasure C.base.Configuration :=
  ⟨C.gibbsMeasure,
    continuous_compact_gauge_gibbsMeasure_isProbabilityMeasure C⟩

@[simp]
theorem continuous_compact_gauge_gibbsProbabilityMeasure_toMeasure
    (C : ContinuousCompactGaugeWilsonSystem) :
    (C.gibbsProbabilityMeasure : Measure C.base.Configuration) =
      C.gibbsMeasure :=
  rfl

end

end MathlibAnalytic
end MGAP4D
