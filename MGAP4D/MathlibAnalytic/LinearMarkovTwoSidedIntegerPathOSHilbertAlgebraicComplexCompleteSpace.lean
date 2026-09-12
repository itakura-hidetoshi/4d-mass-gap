import MGAP4D.MathlibAnalytic.RealTensorComplexificationRealImagCompleteSpace
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexInnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The real-imaginary `L²` coordinate model for the completed temporal OS
Hilbert space after algebraic complexification. -/
abbrev HilbertAlgebraicComplexificationRealImagProduct
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :=
  RealTensorComplexification.RealImagProduct D.Hilbert

/-- Canonical real-linear isometric equivalence between the temporal OS
algebraic complexification and its real-imaginary `L²` coordinate model. -/
def hilbertAlgebraicComplexificationRealImagLinearIsometryEquiv
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.HilbertAlgebraicComplexification ≃ₗᵢ[ℝ]
      D.HilbertAlgebraicComplexificationRealImagProduct :=
  RealTensorComplexification.realImagLinearIsometryEquiv

@[simp] theorem hilbertAlgebraicComplexificationRealImagLinearIsometryEquiv_tmul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (z : ℂ) (x : D.Hilbert) :
    D.hilbertAlgebraicComplexificationRealImagLinearIsometryEquiv
        (z ⊗ₜ[ℝ] x) =
      WithLp.toLp 2 (z.re • x, z.im • x) :=
  RealTensorComplexification.toRealImagLinear_tmul z x

/-- The algebraic complexification of the completed temporal OS Hilbert space
is already complete. No additional completion type is required. -/
theorem hilbertAlgebraicComplexification_completeSpace
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    CompleteSpace D.HilbertAlgebraicComplexification :=
  inferInstance

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
