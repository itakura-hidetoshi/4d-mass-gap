import MGAP4D.MathlibAnalytic.RealTensorComplexificationComplexInnerProductSpace
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexInnerPrecursor

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The standard complex inner product is definitionally the previously
constructed candidate inner product on the temporal OS algebraic
complexification. -/
@[simp] theorem hilbertAlgebraicComplexification_inner_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.HilbertAlgebraicComplexification) :
    inner ℂ x y =
      D.hilbertAlgebraicComplexificationComplexInner x y :=
  rfl

@[simp] theorem hilbertAlgebraicComplexification_inner_re
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.HilbertAlgebraicComplexification) :
    (inner ℂ x y).re =
      RealTensorComplexification.realInner x y :=
  RealTensorComplexification.inner_complex_re x y

@[simp] theorem hilbertAlgebraicComplexification_inner_self
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    inner ℂ x x =
      (RealTensorComplexification.realInner x x : ℂ) :=
  RealTensorComplexification.inner_complex_self x

/-- The pre-existing tensor norm is the norm induced by the installed complex
inner product. -/
theorem hilbertAlgebraicComplexification_norm_sq_eq_re_inner
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    ‖x‖ ^ 2 = (inner ℂ x x).re :=
  InnerProductSpace.norm_sq_eq_re_inner x

/-- The canonical orthogonal complex structure is exactly multiplication by
`i` in the installed complex inner-product space. -/
@[simp] theorem hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry_apply
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x =
      Complex.I • x :=
  RealTensorComplexification.imaginaryUnitLinearIsometry_apply_eq_smul x

/-- Complex scalar multiplication uses the unchanged tensor norm. -/
@[simp] theorem hilbertAlgebraicComplexification_norm_smul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (c : ℂ)
    (x : D.HilbertAlgebraicComplexification) :
    ‖c • x‖ = ‖c‖ * ‖x‖ :=
  RealTensorComplexification.norm_complex_smul c x

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
