import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathMeasure
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPositiveTimeOS

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The actual finite Wilson Gibbs-stationary random-scan two-sided path law is
Osterwalder--Schrader reflection positive on its generated positive-time cylinder
algebra. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    0 ≤ ∫ path,
      ((F : (ℕ → L.Configuration) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path))) *
      ((F : (ℕ → L.Configuration) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂L.randomScanTwoSidedIntegerPathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
  exact linearMarkovTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F

end

end MathlibAnalytic
end MGAP4D
