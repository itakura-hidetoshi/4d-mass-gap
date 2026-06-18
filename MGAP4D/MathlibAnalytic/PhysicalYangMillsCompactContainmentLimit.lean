import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- Quantitative uniform compact containment for the embedded lattice
Yang--Mills laws.  The increasing compact cores capture every lattice law with
a scale-uniform tail bound tending to zero. -/
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

end

end MathlibAnalytic
end MGAP4D
