import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example :
    CompleteSpace
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  inferInstance

example :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n

example (z : ℂ) (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap
        (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] L.randomScanTwoSidedIntegerPathOSHilbertShift x := by
  simp

example (n : ℕ) (z : ℂ) (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n
        (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x := by
  simp

example
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_le x

example (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_le n x

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap 0 = 1 := by
  simp

example (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_add m n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ^ n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_eq_pow n

end

end MathlibAnalytic
end MGAP4D
