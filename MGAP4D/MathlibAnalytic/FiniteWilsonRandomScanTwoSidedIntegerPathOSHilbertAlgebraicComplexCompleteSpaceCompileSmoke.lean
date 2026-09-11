import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexCompleteSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge] :
    InnerProductSpace ℂ
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  inferInstance

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge] :
    CompleteSpace
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  inferInstance

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (z : ℂ)
    (x : L.randomScanTwoSidedIntegerPathOSPreHilbertData.Hilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv
        (z ⊗ₜ[ℝ] x) =
      WithLp.toLp 2 (z.re • x, z.im • x) :=
  L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv_tmul z x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationRealImagLinearIsometryEquiv x‖ =
      ‖x‖ := by
  exact LinearIsometryEquiv.norm_map _ x

end

end MathlibAnalytic
end MGAP4D
