import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexInnerPrecursor

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical orthogonal complex structure on the actual finite Wilson
random-scan algebraic temporal OS complexification. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →ₗᵢ[ℝ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry

/-- Candidate complex inner product on the actual finite Wilson random-scan
algebraic temporal OS complexification. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) : ℂ :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationComplexInner x y

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner_re
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner x y).re =
      inner ℝ x y :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationComplexInner_re x y

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner_self
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner x x =
      (inner ℝ x x : ℂ) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationComplexInner_self x

/-- The algebraically complexified actual finite Wilson one-step temporal OS
shift commutes with the canonical complex structure. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification_map_imaginaryUnit
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification
        (L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification x) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftAlgebraicComplexification_map_imaginaryUnit x

/-- Every natural-time algebraically complexified actual finite Wilson temporal
OS operator commutes with the canonical complex structure. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_map_imaginaryUnit
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n
        (L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n x) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_map_imaginaryUnit n x

end

end MathlibAnalytic
end MGAP4D
