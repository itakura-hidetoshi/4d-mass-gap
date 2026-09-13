import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabSourceLikelihoodRatioFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorCrossRatioCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The source-conditioned one-slab-kernel ratio appearing in the physical
continuous-vacuum covariance localizes pointwise into an `A`-independent
right-boundary spatial factor times the one-link Wilson crossing ratio at the
source.  This is the exact ratio form of the division-free likelihood-ratio
identity from the raw one-slab kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_ratio_eq_spatialHalfUpdateFactor_ratio_mul_crossingRatio
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source h) /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source k) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      (specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k) := by
  have hpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_pairwise_likelihoodRatio
      H N beta A B source h k
  have hQk :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source k) ≠ 0 := by
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta A (Function.update B source k))
  have hSk :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k ≠ 0 := by
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_pos
        H N beta B source k)
  have hrk : specialUnitaryWilsonRelativeKernel N beta (A source) k ≠ 0 := by
    unfold specialUnitaryWilsonRelativeKernel
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact ne_of_gt (Real.exp_pos _)
  field_simp [hQk, hSk, hrk] <;> nlinarith [hpair]

end

end MathlibAnalytic
end MGAP4D
