import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSpectrumInterval
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ENNReal NNReal

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The real spectral radius of every natural-time temporal OS operator equals
its operator `nnnorm`. -/
theorem hilbertShiftSemigroup_spectralRadius_eq_nnnorm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    spectralRadius ℝ (D.hilbertShiftSemigroup n) =
      (‖D.hilbertShiftSemigroup n‖₊ : ℝ≥0∞) :=
  ContinuousLinearMap.spectralRadius_eq_nnnorm
    (D.hilbertShiftSemigroup_isSelfAdjoint hquad n)

/-- Every natural-time temporal OS operator has `nnnorm` at most one. -/
theorem hilbertShiftSemigroup_nnnorm_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ‖D.hilbertShiftSemigroup n‖₊ ≤ 1 := by
  exact_mod_cast D.hilbertShiftSemigroup_opNorm_le_one n

/-- Every natural-time temporal OS spectral radius is at most one. -/
theorem hilbertShiftSemigroup_spectralRadius_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    spectralRadius ℝ (D.hilbertShiftSemigroup n) ≤ 1 := by
  rw [D.hilbertShiftSemigroup_spectralRadius_eq_nnnorm hquad n]
  exact_mod_cast D.hilbertShiftSemigroup_nnnorm_le_one n

/-- The finite real value of every natural-time temporal OS spectral radius is
exactly the operator norm. -/
theorem hilbertShiftSemigroup_spectralRadius_toReal_eq_norm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    (spectralRadius ℝ (D.hilbertShiftSemigroup n)).toReal =
      ‖D.hilbertShiftSemigroup n‖ := by
  rw [D.hilbertShiftSemigroup_spectralRadius_eq_nnnorm hquad n]
  simp

/-- Every natural-time temporal OS spectral radius belongs to `[0, 1]`. -/
theorem hilbertShiftSemigroup_spectralRadius_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    spectralRadius ℝ (D.hilbertShiftSemigroup n) ∈
      Set.Icc (0 : ℝ≥0∞) 1 :=
  ⟨bot_le, D.hilbertShiftSemigroup_spectralRadius_le_one hquad n⟩

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
