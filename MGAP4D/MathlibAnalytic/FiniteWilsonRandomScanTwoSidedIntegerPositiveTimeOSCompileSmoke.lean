import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPositiveTimeOS

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

example
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
      ∂L.randomScanTwoSidedIntegerPathMeasure :=
  finite_lattice_randomScanTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
    L F

end

end MathlibAnalytic
end MGAP4D
