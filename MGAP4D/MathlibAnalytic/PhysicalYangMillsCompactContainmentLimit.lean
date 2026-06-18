import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

structure PhysicalYangMillsCompactCoreScale
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  compactCore : ℕ → Set E.PhysicalConfiguration
  compactCore_isCompact : ∀ m, IsCompact (compactCore m)
  compactCore_monotone : Monotone compactCore
  tailBound : ℕ → ℝ≥0
  tailBound_tendsto_zero : Tendsto tailBound atTop (nhds 0)

end
end MathlibAnalytic
end MGAP4D
