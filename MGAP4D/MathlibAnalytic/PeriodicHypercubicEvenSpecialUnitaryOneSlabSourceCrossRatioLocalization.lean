import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- RED specification: the left-boundary four-point cross-ratio of two
source-conditioned raw one-slab kernels is carried exactly by the single
crossing Wilson relative kernel at the updated source link.

This is deliberately division-free.  In particular, no target link or
source-target distance occurs in the identity: the raw source-conditioned
ratio oscillation is source-local. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_leftBoundary_crossRatio_localizes
    (H N : ℕ)
    (beta : ℝ)
    (A A' B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source h) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A'
          (Function.update B source k) *
        (specialUnitaryWilsonRelativeKernel N beta (A source) k *
          specialUnitaryWilsonRelativeKernel N beta (A' source) h) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source k) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A'
          (Function.update B source h) *
        (specialUnitaryWilsonRelativeKernel N beta (A source) h *
          specialUnitaryWilsonRelativeKernel N beta (A' source) k) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
