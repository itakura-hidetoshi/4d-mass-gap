import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- With exactly constant input, left Hamiltonian tracking decays at the full
spectral-gap rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ)) := by
  have hrate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
      b a δ hδ hδpos t₀ t ht A (fun _ : ℝ => F_lim) U F_lim 0
      continuous_const (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
  simpa [mul_comm] using hrate

/-- With exactly constant input, right Hamiltonian tracking has the same full-gap
rate and needs no commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ)) := by
  have hrate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
      b a δ hδ hδpos t₀ t ht A (fun _ : ℝ => F_lim) U F_lim 0
      continuous_const (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
  simpa [mul_comm] using hrate

end

end MathlibAnalytic
end MGAP4D
