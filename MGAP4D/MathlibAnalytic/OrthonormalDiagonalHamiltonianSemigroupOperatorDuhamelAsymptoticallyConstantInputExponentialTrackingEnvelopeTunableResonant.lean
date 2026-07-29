import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeTunableResonantScalar
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeResonant

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Resonant left tracking at any prescribed slower positive rate `ν < δ`, with the
sharp forcing constant for that rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_tunable_resonant_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ ν : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (hνpos : 0 < ν) (hνδ : ν < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / (Real.exp 1 * (δ - ν))) *
        Real.exp (-((t - t₀) * ν)) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤ Real.exp (-((t - t₀) * ν)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sub_nonneg.mpr ht]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * ν)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_one_div_exp_one_mul_sub_mul_exp_rate δ ν (t - t₀) hνδ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((1 / (Real.exp 1 * (δ - ν))) *
          Real.exp (-((t - t₀) * ν))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * ν)) * ‖A - S‖ +
          ((1 / (Real.exp 1 * (δ - ν))) *
            Real.exp (-((t - t₀) * ν))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / (Real.exp 1 * (δ - ν))) *
        Real.exp (-((t - t₀) * ν)) := by
      simp [S]
      ring

/-- Resonant right tracking at any prescribed slower positive rate `ν < δ`, with the
same sharp forcing constant for that rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_tunable_resonant_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ ν : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (hνpos : 0 < ν) (hνδ : ν < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / (Real.exp 1 * (δ - ν))) *
        Real.exp (-((t - t₀) * ν)) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤ Real.exp (-((t - t₀) * ν)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sub_nonneg.mpr ht]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * ν)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_one_div_exp_one_mul_sub_mul_exp_rate δ ν (t - t₀) hνδ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((1 / (Real.exp 1 * (δ - ν))) *
          Real.exp (-((t - t₀) * ν))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * ν)) * ‖A - S‖ +
          ((1 / (Real.exp 1 * (δ - ν))) *
            Real.exp (-((t - t₀) * ν))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / (Real.exp 1 * (δ - ν))) *
        Real.exp (-((t - t₀) * ν)) := by
      simp [S]
      ring

end

end MathlibAnalytic
end MGAP4D
