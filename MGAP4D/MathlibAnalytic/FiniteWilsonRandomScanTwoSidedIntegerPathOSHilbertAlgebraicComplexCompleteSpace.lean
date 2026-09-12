import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexInnerProductSpace
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexCompleteSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

/-- The real-imaginary `L²` coordinate model for the actual finite Wilson
random-scan temporal OS algebraic complexification. -/
abbrev FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagProduct
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.HilbertAlgebraicComplexificationRealImagProduct

/-- Canonical real-linear isometric equivalence for the actual finite Wilson
random-scan temporal OS algebraic complexification. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification ≃ₗᵢ[ℝ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagProduct :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationRealImagLinearIsometryEquiv

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv_tmul
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (z : ℂ)
    (x : L.randomScanTwoSidedIntegerPathOSPreHilbertData.Hilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv
        (z ⊗ₜ[ℝ] x) =
      WithLp.toLp 2 (z.re • x, z.im • x) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationRealImagLinearIsometryEquiv_tmul z x

/-- The actual finite Wilson random-scan temporal OS algebraic complexification
is already a complete complex inner-product space. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_completeSpace
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    CompleteSpace L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  inferInstance

end

end MathlibAnalytic
end MGAP4D
