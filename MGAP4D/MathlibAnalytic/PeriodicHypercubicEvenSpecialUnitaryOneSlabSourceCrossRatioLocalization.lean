import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The four-point left-boundary cross-ratio of the exact right-update local
Boltzmann factors is carried by the single Wilson crossing kernel at the
updated source link.

The spatial right-boundary action increment and the reference crossing energy
against `B source` cancel pairwise.  Thus only the four source-link crossing
energies involving `A source`, `A' source`, `h`, and `k` remain. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_source_update_leftBoundary_crossRatio_localizes
    (H N : ℕ)
    (beta : ℝ)
    (A A' B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A' B source k *
        (specialUnitaryWilsonRelativeKernel N beta (A source) k *
          specialUnitaryWilsonRelativeKernel N beta (A' source) h) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A' B source h *
        (specialUnitaryWilsonRelativeKernel N beta (A source) h *
          specialUnitaryWilsonRelativeKernel N beta (A' source) k) := by
  simp only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
    specialUnitaryWilsonRelativeKernel,
    specialUnitaryWilsonBoltzmannCentralFunction,
    ← Real.exp_add]
  congr 1
  ring

/-- The left-boundary four-point cross-ratio of two source-conditioned raw
one-slab kernels is carried exactly by the single crossing Wilson relative
kernel at the updated source link.

This identity is division-free and contains no target link or source-target
distance.  Hence the raw source-conditioned ratio oscillation is source-local;
any later distance decay must enter through the integration/correlation layer,
not through this raw pairwise kernel ratio alone. -/
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
  simp only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_source_update_leftBoundary_crossRatio_localizes
      H N beta A A' B source h k
  calc
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A' B source k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A' B) *
      (specialUnitaryWilsonRelativeKernel N beta (A source) k *
        specialUnitaryWilsonRelativeKernel N beta (A' source) h) =
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B source h *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A' B source k *
            (specialUnitaryWilsonRelativeKernel N beta (A source) k *
              specialUnitaryWilsonRelativeKernel N beta (A' source) h)) *
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A' B) := by
      ring
    _ =
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B source k *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A' B source h *
            (specialUnitaryWilsonRelativeKernel N beta (A source) h *
              specialUnitaryWilsonRelativeKernel N beta (A' source) k)) *
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A' B) := by
      rw [hLocal]
    _ =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A' B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A' B) *
      (specialUnitaryWilsonRelativeKernel N beta (A source) h *
        specialUnitaryWilsonRelativeKernel N beta (A' source) k) := by
      ring

end

end MathlibAnalytic
end MGAP4D
