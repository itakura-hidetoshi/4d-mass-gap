import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Under exactly constant input, left Hamiltonian evolution converges to its
steady state at the full spectral-gap rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ε' := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  refine ⟨t₀ + max 0
      (Real.log
        (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ / ε') / δ), ?_⟩
  intro t ht
  have hle :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ A U F_lim hU0 hU ε' hε' t ht
  have hlt :
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ < ε := by
    exact lt_of_le_of_lt hle (by dsimp [ε']; linarith)
  simpa [dist_eq_norm] using hlt

/-- Under exactly constant input, right Hamiltonian evolution converges to its
steady state at the same full spectral-gap rate, without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ε' := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  refine ⟨t₀ + max 0
      (Real.log
        (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ / ε') / δ), ?_⟩
  intro t ht
  have hle :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ A U F_lim hU0 hU ε' hε' t ht
  have hlt :
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ < ε := by
    exact lt_of_le_of_lt hle (by dsimp [ε']; linarith)
  simpa [dist_eq_norm] using hlt

end

end MathlibAnalytic
end MGAP4D
