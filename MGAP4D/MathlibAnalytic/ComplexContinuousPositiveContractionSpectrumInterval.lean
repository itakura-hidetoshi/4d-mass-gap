import MGAP4D.MathlibAnalytic.ComplexContinuousSymmetricContractionLoewnerInterval
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A pointwise complex contraction has operator norm at most one. -/
theorem opNorm_le_one
    (T : H →L[ℂ] H)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖) :
    ‖T‖ ≤ 1 :=
  T.opNorm_le_bound zero_le_one fun x => by
    simpa using hcontract x

/-- The identity operator has norm at most one, including on a degenerate
Hilbert space. -/
theorem identity_opNorm_le_one :
    ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  (1 : H →L[ℂ] H).opNorm_le_bound zero_le_one fun x => by
    simp

section Complete

variable [CompleteSpace H]

/-- Every real spectral value of a positive complex continuous linear map is
nonnegative. -/
theorem real_spectrum_nonneg
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ T) :
    0 ≤ r :=
  spectrum_nonneg_of_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive) hr

/-- Every real spectral value of a pointwise complex contraction is at most
one. -/
theorem real_spectrum_le_one
    (T : H →L[ℂ] H)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ T) :
    r ≤ 1 := by
  calc
    r ≤ ‖r‖ := Real.le_norm_self r
    _ ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ :=
      spectrum.norm_le_norm_mul_of_mem hr
    _ ≤ 1 * 1 :=
      mul_le_mul
        (opNorm_le_one T hcontract)
        identity_opNorm_le_one
        (norm_nonneg _)
        zero_le_one
    _ = 1 := by norm_num

/-- Every complex spectral value of a positive complex contraction belongs to
`[0, 1]` in the complex order. -/
theorem complex_spectrum_mem_Icc
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖)
    {c : ℂ}
    (hc : c ∈ spectrum ℂ T) :
    c ∈ Set.Icc (0 : ℂ) 1 := by
  have hc0 : 0 ≤ c :=
    spectrum_nonneg_of_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive) hc
  have hnorm : ‖c‖ ≤ 1 := by
    calc
      ‖c‖ ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ :=
        spectrum.norm_le_norm_mul_of_mem hc
      _ ≤ 1 * 1 :=
        mul_le_mul
          (opNorm_le_one T hcontract)
          identity_opNorm_le_one
          (norm_nonneg _)
          zero_le_one
      _ = 1 := by norm_num
  have hreal : (c.re : ℂ) = c :=
    hpositive.isSelfAdjoint.spectrumRestricts.rightInvOn hc
  have hre_norm : |c.re| ≤ 1 := by
    rw [← hreal] at hnorm
    simpa using hnorm
  constructor
  · exact hc0
  · refine (RCLike.le_iff_re_im).2 ⟨?_, ?_⟩
    · simpa using (le_abs_self c.re).trans hre_norm
    · have him := congrArg Complex.im hreal
      simpa using him.symm

/-- The complex spectrum of a positive complex contraction is contained in the
closed unit interval. -/
theorem complex_spectrum_subset_Icc
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖) :
    spectrum ℂ T ⊆ Set.Icc (0 : ℂ) 1 := by
  intro c hc
  exact complex_spectrum_mem_Icc T hpositive hcontract hc

end Complete

end ComplexContinuousPositiveContraction

end

end MathlibAnalytic
end MGAP4D
