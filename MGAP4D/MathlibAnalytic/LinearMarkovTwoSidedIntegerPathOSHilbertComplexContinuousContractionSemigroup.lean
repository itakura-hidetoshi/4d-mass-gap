import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousContraction
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexCompleteSpace
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSymmetricContractionSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Continuous complex-linear extension of the one-step temporal OS shift. -/
noncomputable def hilbertShiftComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.HilbertAlgebraicComplexification →L[ℂ]
      D.HilbertAlgebraicComplexification :=
  RealTensorComplexification.ofContinuousLinearMapContraction
    D.hilbertShiftContinuousLinearMap
    (fun x => D.norm_hilbertShiftContinuousLinearMap_le x)

/-- Continuous complex-linear discrete temporal OS semigroup. -/
noncomputable def hilbertShiftSemigroupComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.HilbertAlgebraicComplexification →L[ℂ]
      D.HilbertAlgebraicComplexification :=
  RealTensorComplexification.ofContinuousLinearMapContraction
    (D.hilbertShiftSemigroup n)
    (fun x => D.norm_hilbertShiftSemigroup_le n x)

@[simp] theorem hilbertShiftComplexContinuousLinearMap_apply
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertShiftComplexContinuousLinearMap x =
      D.hilbertShiftAlgebraicComplexification x :=
  rfl

@[simp] theorem hilbertShiftSemigroupComplexContinuousLinearMap_apply
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.HilbertAlgebraicComplexification) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap n x =
      D.hilbertShiftSemigroupAlgebraicComplexification n x :=
  rfl

@[simp] theorem hilbertShiftComplexContinuousLinearMap_tmul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (z : ℂ)
    (x : D.Hilbert) :
    D.hilbertShiftComplexContinuousLinearMap (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] D.hilbertShiftContinuousLinearMap x := by
  rfl

@[simp] theorem hilbertShiftSemigroupComplexContinuousLinearMap_tmul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (z : ℂ)
    (x : D.Hilbert) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap n (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] D.hilbertShiftSemigroup n x := by
  rfl

/-- The complexified one-step shift is a contraction. -/
theorem norm_hilbertShiftComplexContinuousLinearMap_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    ‖D.hilbertShiftComplexContinuousLinearMap x‖ ≤ ‖x‖ :=
  RealTensorComplexification.norm_ofContinuousLinearMapContraction_le
    D.hilbertShiftContinuousLinearMap
    (fun y => D.norm_hilbertShiftContinuousLinearMap_le y) x

/-- Every complexified natural-time temporal OS operator is a contraction. -/
theorem norm_hilbertShiftSemigroupComplexContinuousLinearMap_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.HilbertAlgebraicComplexification) :
    ‖D.hilbertShiftSemigroupComplexContinuousLinearMap n x‖ ≤ ‖x‖ :=
  RealTensorComplexification.norm_ofContinuousLinearMapContraction_le
    (D.hilbertShiftSemigroup n)
    (fun y => D.norm_hilbertShiftSemigroup_le n y) x

@[simp] theorem hilbertShiftSemigroupComplexContinuousLinearMap_zero
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap 0 = 1 := by
  ext x
  change D.hilbertShiftSemigroupAlgebraicComplexification 0 x = x
  rw [D.hilbertShiftSemigroupAlgebraicComplexification_zero]
  rfl

@[simp] theorem hilbertShiftSemigroupComplexContinuousLinearMap_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap 1 =
      D.hilbertShiftComplexContinuousLinearMap := by
  ext x
  change D.hilbertShiftSemigroupAlgebraicComplexification 1 x =
    D.hilbertShiftAlgebraicComplexification x
  rw [D.hilbertShiftSemigroupAlgebraicComplexification_one]

@[simp] theorem hilbertShiftSemigroupComplexContinuousLinearMap_succ
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap (n + 1) =
      D.hilbertShiftComplexContinuousLinearMap.comp
        (D.hilbertShiftSemigroupComplexContinuousLinearMap n) := by
  ext x
  change D.hilbertShiftSemigroupAlgebraicComplexification (n + 1) x =
    D.hilbertShiftAlgebraicComplexification
      (D.hilbertShiftSemigroupAlgebraicComplexification n x)
  rw [D.hilbertShiftSemigroupAlgebraicComplexification_succ]
  rfl

/-- The continuous complex temporal OS operators retain the additive semigroup law. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_add
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (m n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap (m + n) =
      (D.hilbertShiftSemigroupComplexContinuousLinearMap m).comp
        (D.hilbertShiftSemigroupComplexContinuousLinearMap n) := by
  ext x
  change D.hilbertShiftSemigroupAlgebraicComplexification (m + n) x =
    D.hilbertShiftSemigroupAlgebraicComplexification m
      (D.hilbertShiftSemigroupAlgebraicComplexification n x)
  rw [D.hilbertShiftSemigroupAlgebraicComplexification_add]
  rfl

/-- Any two members of the continuous complex temporal OS semigroup commute. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_comp_comm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (m n : ℕ) :
    (D.hilbertShiftSemigroupComplexContinuousLinearMap m).comp
        (D.hilbertShiftSemigroupComplexContinuousLinearMap n) =
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n).comp
        (D.hilbertShiftSemigroupComplexContinuousLinearMap m) := by
  rw [← D.hilbertShiftSemigroupComplexContinuousLinearMap_add,
    Nat.add_comm,
    D.hilbertShiftSemigroupComplexContinuousLinearMap_add]

/-- The continuous complex temporal OS semigroup is generated by its one-step member. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_eq_pow
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap n =
      D.hilbertShiftComplexContinuousLinearMap ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [D.hilbertShiftSemigroupComplexContinuousLinearMap_succ,
        ih,
        pow_succ']
      rfl

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
