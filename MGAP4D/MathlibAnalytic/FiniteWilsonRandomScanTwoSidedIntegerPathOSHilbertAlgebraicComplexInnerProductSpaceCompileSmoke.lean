import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexInnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge] :
    InnerProductSpace ℂ
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  inferInstance

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    star (inner ℂ y x) = inner ℂ x y := by
  exact inner_conj_symm x y

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (c : ℂ)
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ (c • x) y = star c * inner ℂ x y := by
  exact inner_smul_left (𝕜 := ℂ) x y (r := c)

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (c : ℂ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖c • x‖ = ‖c‖ * ‖x‖ :=
  L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification_norm_smul c x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x =
      Complex.I • x :=
  L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry_apply x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n
        (Complex.I • x) =
      Complex.I •
        L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n x := by
  exact LinearMap.map_smul
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n)
    Complex.I x

end

end MathlibAnalytic
end MGAP4D
