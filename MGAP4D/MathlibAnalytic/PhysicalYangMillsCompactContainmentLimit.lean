import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- Quantitative uniform compact containment for the embedded lattice
Yang--Mills laws. -/
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

end

end MathlibAnalytic
end MGAP4D
