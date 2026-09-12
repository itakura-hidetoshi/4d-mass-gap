import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexCompleteSpace
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

/-- Continuous complex-linear one-step temporal OS shift for the actual finite
Wilson random-scan system. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap

/-- Continuous complex-linear discrete temporal OS semigroup for the actual
finite Wilson random-scan system. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap n

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification x :=
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n x :=
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_tmul
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (z : ℂ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap
        (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] L.randomScanTwoSidedIntegerPathOSHilbertShift x := by
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_tmul
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (z : ℂ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n
        (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x := by
  rfl

/-- The actual finite Wilson complexified one-step temporal OS shift is a
contraction. -/
theorem FiniteLatticeWilsonSystem.norm_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x‖ ≤ ‖x‖ :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.norm_hilbertShiftComplexContinuousLinearMap_le x

/-- Every actual finite Wilson complexified natural-time temporal OS operator
is a contraction. -/
theorem FiniteLatticeWilsonSystem.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x‖ ≤ ‖x‖ :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n x

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap 0 = 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_zero

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_one

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_succ
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap (n + 1) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap.comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_succ n

/-- The actual finite Wilson continuous complex temporal OS operators retain
the additive semigroup law. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_add
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_add m n

/-- Any two actual finite Wilson continuous complex temporal OS operators
commute. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_comp_comm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap m) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_comp_comm m n

/-- The actual finite Wilson continuous complex temporal OS semigroup is
generated by its one-step member. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_eq_pow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ^ n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_eq_pow n

end

end MathlibAnalytic
end MGAP4D
