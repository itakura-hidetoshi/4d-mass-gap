import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathDistinctFiberTransportCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceDistinctFiberOffFiberTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- RED probe: changing one left-background spatial link changes the literal C5
reference weight by at most the volume-independent factor `exp (32 * beta)`.
The factor keeps the three physical pieces separate: continuous vacuum,
right-target local factor, and one-slab kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber g) ≤
        Real.exp (32 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂
            (Function.update A backgroundFiber h) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber h) ≤
        Real.exp (32 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂
            (Function.update A backgroundFiber g) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
