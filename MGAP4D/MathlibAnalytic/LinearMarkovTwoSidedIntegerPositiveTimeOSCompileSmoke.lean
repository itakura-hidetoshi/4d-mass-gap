import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPositiveTimeOS

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

example {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    0 ≤ ∫ path,
      ((F : (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path))) *
      ((F : (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb :=
  linearMarkovTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
    initial transition hdb F

end

end MathlibAnalytic
end MGAP4D
