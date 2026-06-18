import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- The pushed-forward lattice Yang--Mills laws form a tight family on the fixed
physical configuration space. -/
def PhysicalFourDimensionalYangMillsLatticeEmbedding.IsTight
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) : Prop :=
  IsTightMeasureSet
    {((μ : ProbabilityMeasure E.PhysicalConfiguration) :
        Measure E.PhysicalConfiguration) |
      μ ∈ Set.range E.embeddedMeasure}

/-- A Prokhorov subsequential limit extracted from the embedded lattice laws. -/
structure PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  weakConvergence :
    Tendsto (fun n => E.embeddedMeasure (subsequence n)) atTop
      (nhds continuumMeasure)

/-- Mathlib Prokhorov compactness turns tightness of the embedded Wilson laws
into an actual convergent subsequence and a continuum probability measure. -/
theorem physical_yang_mills_prokhorov_subsequence_exists
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (hTight : E.IsTight) :
    Nonempty (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E) := by
  have hCompact :
      IsCompact (closure (Set.range E.embeddedMeasure)) :=
    isCompact_closure_of_isTightMeasureSet hTight
  obtain ⟨continuumMeasure, _hmem, subsequence,
      subsequence_strictMono, weakConvergence⟩ :=
    hCompact.isSeqCompact
      (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨{
    continuumMeasure := continuumMeasure
    subsequence := subsequence
    subsequence_strictMono := subsequence_strictMono
    weakConvergence := weakConvergence }⟩

/-- The Prokhorov subsequence remains a physical scaling sequence: lattice
spacing still tends to zero and physical volume still tends to infinity. -/
noncomputable def
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit.toWeakLimit
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  { Configuration := E.PhysicalConfiguration
    approximatingMeasure := fun n => E.embeddedMeasure (L.subsequence n)
    continuumMeasure := L.continuumMeasure
    weakConvergence := L.weakConvergence
    latticeSpacing := fun n => E.latticeSpacing (L.subsequence n)
    latticeSpacing_pos := fun n => E.latticeSpacing_pos (L.subsequence n)
    latticeSpacing_tendsto_zero :=
      E.latticeSpacing_tendsto_zero.comp
        L.subsequence_strictMono.tendsto_atTop
    physicalVolume := fun n => E.physicalVolume (L.subsequence n)
    physicalVolume_tendsto_atTop :=
      E.physicalVolume_tendsto_atTop.comp
        L.subsequence_strictMono.tendsto_atTop }

/-- Tightness alone now produces a physical continuum weak-limit carrier,
noncomputably choosing a Prokhorov subsequence. -/
noncomputable def physical_yang_mills_weak_limit_of_tight
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (hTight : E.IsTight) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (physical_yang_mills_prokhorov_subsequence_exists E hTight).some.toWeakLimit

/-- Concrete specialization: tightness of the interpolated compact-gauge Wilson
Gibbs laws is sufficient for existence of a subsequential continuum probability
measure on the fixed physical carrier. -/
noncomputable def continuous_compact_gauge_wilson_weak_limit_of_tight
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_tight E.toLatticeEmbedding hTight

end

end MathlibAnalytic
end MGAP4D
