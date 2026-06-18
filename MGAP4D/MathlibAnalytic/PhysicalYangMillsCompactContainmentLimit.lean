import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- Quantitative uniform compact containment for the embedded lattice
Yang--Mills laws.

The increasing compact sets `compactCore m` capture all lattice laws up to the
uniform tail `tailBound m`, and the tail tends to zero.  This is the concrete
analytic estimate needed by Prokhorov compactness. -/
structure PhysicalYangMillsUniformCompactContainment
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  compactCore : ℕ → Set E.PhysicalConfiguration
  compactCore_isCompact : ∀ m, IsCompact (compactCore m)
  compactCore_monotone : Monotone compactCore
  tailBound : ℕ → ℝ≥0
  tailBound_tendsto_zero : Tendsto tailBound atTop (nhds 0)
  measure_compl_le :
    ∀ (latticeScale compactScale : ℕ),
      E.embeddedMeasure latticeScale (compactCore compactScale)ᶜ ≤
        tailBound compactScale

/-- The quantitative compact-containment class of probability measures is
compact by Mathlib's Prokhorov theorem. -/
theorem physical_yang_mills_compact_containment_measure_set_isCompact
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    IsCompact
      {μ : ProbabilityMeasure E.PhysicalConfiguration |
        ∀ m, μ (C.compactCore m)ᶜ ≤ C.tailBound m} := by
  exact isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    C.tailBound_tendsto_zero C.compactCore_isCompact
    (Or.inr C.compactCore_monotone)

/-- Uniform compact containment directly yields a convergent lattice
subsequence and an actual continuum probability measure. -/
theorem physical_yang_mills_subsequence_exists_of_compact_containment
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    Nonempty (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E) := by
  have hCompact :=
    physical_yang_mills_compact_containment_measure_set_isCompact C
  obtain ⟨continuumMeasure, _hmem, subsequence,
      subsequence_strictMono, weakConvergence⟩ :=
    hCompact.isSeqCompact (fun n m => C.measure_compl_le n m)
  exact ⟨{
    continuumMeasure := continuumMeasure
    subsequence := subsequence
    subsequence_strictMono := subsequence_strictMono
    weakConvergence := weakConvergence }⟩

/-- A physical continuum weak-limit carrier constructed from the explicit
uniform compact-containment estimate. -/
noncomputable def physical_yang_mills_weak_limit_of_compact_containment
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (physical_yang_mills_subsequence_exists_of_compact_containment C).some.toWeakLimit

/-- Concrete compact-gauge Wilson specialization of the quantitative
compact-containment route. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_compact_containment
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (C : PhysicalYangMillsUniformCompactContainment E.toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_compact_containment C

end

end MathlibAnalytic
end MGAP4D
