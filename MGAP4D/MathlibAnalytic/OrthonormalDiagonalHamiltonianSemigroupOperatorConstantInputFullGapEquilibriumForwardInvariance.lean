import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If left constant-input evolution starts at its steady state, it remains there
for every later time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_eq_steadyState_of_initial_eq_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (hA : A = orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) :
    U t = orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ t ht A U F_lim hU0 hU
  have hzero :
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ 0 := by
    simpa [hA] using henv
  have hnorm :
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ = 0 :=
    le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- If right constant-input evolution starts at its steady state, it remains there
for every later time, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_eq_steadyState_of_initial_eq_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (hA : A = orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) :
    U t = orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ t ht A U F_lim hU0 hU
  have hzero :
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ 0 := by
    simpa [hA] using henv
  have hnorm :
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ = 0 :=
    le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
