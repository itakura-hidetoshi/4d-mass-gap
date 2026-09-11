import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexInnerPrecursor
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexInnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson algebraic temporal OS complexification carries the
installed complex inner product without any additional hypothesis. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_inner_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ x y =
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner x y :=
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_inner_re
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (inner ℂ x y).re =
      RealTensorComplexification.realInner x y :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexification_inner_re x y

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_inner_self
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ x x =
      (RealTensorComplexification.realInner x x : ℂ) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexification_inner_self x

/-- The actual finite Wilson algebraic complexification retains the existing
tensor norm as its complex inner-product norm. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_norm_sq_eq_re_inner
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖x‖ ^ 2 = (inner ℂ x x).re :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexification_norm_sq_eq_re_inner x

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry_apply
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x =
      Complex.I • x :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexificationImaginaryUnitLinearIsometry_apply x

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_norm_smul
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (c : ℂ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖c • x‖ = ‖c‖ * ‖x‖ :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertAlgebraicComplexification_norm_smul c x

end

end MathlibAnalytic
end MGAP4D
