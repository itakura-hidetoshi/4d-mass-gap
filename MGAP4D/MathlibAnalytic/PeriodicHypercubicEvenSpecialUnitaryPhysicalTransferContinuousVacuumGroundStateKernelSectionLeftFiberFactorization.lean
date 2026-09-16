import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionContinuousDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Restrict the continuous fixed-right kernel-section density to one left
spatial-link section.  This is a pointwise section of the already-established
continuous density; no a.e. representative is restricted to a fiber here. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
    H N hN beta hbeta C (Function.update A target g)

/-- The nonconstant part of a left one-link section: canonical continuous
vacuum amplitude times the exact one-link Wilson local factor obtained after
using symmetry of the one-slab kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta (Function.update A target g) *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta C A target g

/-- Exact left-section factorization.

For fixed right boundary `C`, base left boundary `A`, and left target link,
the pointwise kernel-section density along `g` is

`Ω_cont(A[target ← g]) * localFactor(C,A,target,g) * K(A,C)`.

The final kernel factor is independent of `g`.  This is the precise algebraic
bridge needed before normalizing the one-link section; no regular conditional
probability statement is made. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_eq_localWeight_mul_baseKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta C A target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
          H N hN beta hbeta C A target g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A C := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta (Function.update A target g) C]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
    H N beta C A target g]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta C A]
  ring

/-- The nonconstant left-section local weight is strictly positive pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
        H N hN beta hbeta C A target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update A target g))
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta C A target g)

/-- Consequently the complete continuous left-section weight is strictly
positive pointwise as well. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta C A target g := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_eq_localWeight_mul_baseKernel]
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight_pos
      H N hN beta hbeta C A target g)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A C)

end

end MathlibAnalytic
end MGAP4D
