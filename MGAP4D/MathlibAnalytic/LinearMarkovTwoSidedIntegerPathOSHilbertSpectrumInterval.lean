import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertLoewnerRayleighInterval
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time temporal OS operator has operator norm at most one. -/
theorem hilbertShiftSemigroup_opNorm_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ‖D.hilbertShiftSemigroup n‖ ≤ 1 :=
  (D.hilbertShiftSemigroup n).opNorm_le_bound zero_le_one fun x => by
    simpa using D.norm_hilbertShiftSemigroup_le n x

/-- Every real spectral value of a natural-time temporal OS operator is
nonnegative. -/
theorem hilbertShiftSemigroup_spectrum_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ (D.hilbertShiftSemigroup n)) :
    0 ≤ c :=
  SpectrumRestricts.nnreal_iff.mp
    (D.hilbertShiftSemigroup_isPositive hquad n).spectrumRestricts c hc

/-- Every real spectral value of a natural-time temporal OS operator is at most
one. -/
theorem hilbertShiftSemigroup_spectrum_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ (D.hilbertShiftSemigroup n)) :
    c ≤ 1 := by
  calc
    c ≤ ‖c‖ := Real.le_norm_self c
    _ ≤ ‖D.hilbertShiftSemigroup n‖ := spectrum.norm_le_norm_of_mem hc
    _ ≤ 1 := D.hilbertShiftSemigroup_opNorm_le_one n

/-- The real spectrum of every natural-time temporal OS operator is contained
in the closed unit interval. -/
theorem hilbertShiftSemigroup_spectrum_subset_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    spectrum ℝ (D.hilbertShiftSemigroup n) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro c hc
  exact ⟨D.hilbertShiftSemigroup_spectrum_nonneg hquad n hc,
    D.hilbertShiftSemigroup_spectrum_le_one n hc⟩

/-- Pointwise form of the temporal OS spectral interval theorem. -/
theorem hilbertShiftSemigroup_spectrum_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ (D.hilbertShiftSemigroup n)) :
    c ∈ Set.Icc (0 : ℝ) 1 :=
  D.hilbertShiftSemigroup_spectrum_subset_Icc hquad n hc

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
