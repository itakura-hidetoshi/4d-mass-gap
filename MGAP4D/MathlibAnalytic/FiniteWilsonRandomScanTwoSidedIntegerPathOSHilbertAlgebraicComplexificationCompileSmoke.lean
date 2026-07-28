import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification 0 = 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_zero

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_one

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_add m n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_comp_comm m n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification ^ n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_eq_pow n

end

end MathlibAnalytic
end MGAP4D
