import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetKernelHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- RED target: transport the sharp raw one-link kernel Harnack bound to the
canonical continuous physical vacuum representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update B target g) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target h) := by
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
