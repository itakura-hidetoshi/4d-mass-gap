import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionLeftFiberRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The complete fixed-right one-link kernel section and its nonconstant local
weight have exactly the same pairwise density ratios.  Thus the positive base
kernel factor is invisible after fiberwise normalization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_div_eq_localWeight_div
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta C A target g₁ /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta C A target g₂ =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
        H N hN beta hbeta C A target g₁ /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
        H N hN beta hbeta C A target g₂ := by
  have hSection₂ :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
          H N hN beta hbeta C A target g₂ ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_pos
        H N hN beta hbeta C A target g₂)
  have hLocal₂ :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
          H N hN beta hbeta C A target g₂ ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight_pos
        H N hN beta hbeta C A target g₂)
  apply (div_eq_div_iff hSection₂ hLocal₂).2
  simpa [mul_comm] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_cross_mul_localWeight
      H N hN beta hbeta C A target g₁ g₂)

end

end MathlibAnalytic
end MGAP4D
