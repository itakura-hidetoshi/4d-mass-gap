import MGAP4D.MathlibAnalytic.RealTensorComplexificationHilbertPrecursor
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The canonical orthogonal complex structure on the algebraic complexification
of the completed temporal OS Hilbert space. -/
noncomputable def hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.HilbertAlgebraicComplexification →ₗᵢ[ℝ]
      D.HilbertAlgebraicComplexification :=
  RealTensorComplexification.imaginaryUnitLinearIsometry

/-- Candidate complex inner product on the algebraic complexification of the
completed temporal OS Hilbert space. -/
def hilbertAlgebraicComplexificationComplexInner
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.HilbertAlgebraicComplexification) : ℂ :=
  RealTensorComplexification.complexInner x y

@[simp] theorem hilbertAlgebraicComplexificationComplexInner_re
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.HilbertAlgebraicComplexification) :
    (D.hilbertAlgebraicComplexificationComplexInner x y).re =
      RealTensorComplexification.realInner x y :=
  RealTensorComplexification.complexInner_re x y

@[simp] theorem hilbertAlgebraicComplexificationComplexInner_self
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertAlgebraicComplexificationComplexInner x x =
      (RealTensorComplexification.realInner x x : ℂ) :=
  RealTensorComplexification.complexInner_self x

/-- The algebraically complexified one-step temporal OS shift commutes with the
canonical complex structure. -/
theorem hilbertShiftAlgebraicComplexification_map_imaginaryUnit
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertShiftAlgebraicComplexification
        (D.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      D.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (D.hilbertShiftAlgebraicComplexification x) :=
  RealTensorComplexification.linearMap_map_imaginaryUnit
    D.hilbertShiftAlgebraicComplexification x

/-- Every natural-time algebraically complexified temporal OS operator commutes
with the canonical complex structure. -/
theorem hilbertShiftSemigroupAlgebraicComplexification_map_imaginaryUnit
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertShiftSemigroupAlgebraicComplexification n
        (D.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      D.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (D.hilbertShiftSemigroupAlgebraicComplexification n x) :=
  RealTensorComplexification.linearMap_map_imaginaryUnit
    (D.hilbertShiftSemigroupAlgebraicComplexification n) x

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
